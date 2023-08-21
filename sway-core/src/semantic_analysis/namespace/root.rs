use sway_error::{
    error::CompileError,
    handler::{ErrorEmitted, Handler},
};
use sway_types::Spanned;
use sway_utils::iter_prefixes;

use crate::{
    decl_engine::DeclRef,
    language::{
        ty::{self, TypeDecl},
        CallPath,
    },
    Engines, Ident, TypeId, TypeInfo,
};

use super::{module::Module, namespace::Namespace, Path};

/// The root module, from which all other modules can be accessed.
///
/// This is equivalent to the "crate root" of a Rust crate.
///
/// We use a custom type for the `Root` in order to ensure that methods that only work with
/// canonical paths, or that use canonical paths internally, are *only* called from the root. This
/// normally includes methods that first lookup some canonical path via `use_synonyms` before using
/// that canonical path to look up the symbol declaration.
#[derive(Clone, Debug)]
pub struct Root {
    pub(crate) module: Module,
}

impl Root {
    /// Resolve a symbol that is potentially prefixed with some path, e.g. `foo::bar::symbol`.
    ///
    /// This is short-hand for concatenating the `mod_path` with the `call_path`'s prefixes and
    /// then calling `resolve_symbol` with the resulting path and call_path's suffix.
    pub(crate) fn resolve_call_path(
        &self,
        handler: &Handler,
        engines: &Engines,
        mod_path: &Path,
        call_path: &CallPath,
    ) -> Result<ty::TyDecl, ErrorEmitted> {
        let (decl, _) =
            self.resolve_call_path_and_mod_path(handler, engines, mod_path, call_path, None)?;
        Ok(decl)
    }

    fn resolve_call_path_and_mod_path(
        &self,
        handler: &Handler,
        engines: &Engines,
        mod_path: &Path,
        call_path: &CallPath,
        self_type: Option<TypeId>,
    ) -> Result<(ty::TyDecl, Vec<Ident>), ErrorEmitted> {
        let symbol_path: Vec<_> = mod_path
            .iter()
            .chain(&call_path.prefixes)
            .cloned()
            .collect();
        self.resolve_symbol_and_mod_path(
            handler,
            engines,
            &symbol_path,
            &call_path.suffix,
            self_type,
        )
    }

    /// Resolve a symbol that is potentially prefixed with some path, e.g. `foo::bar::symbol`.
    ///
    /// This will concatenate the `mod_path` with the `call_path`'s prefixes and
    /// then calling `resolve_symbol` with the resulting path and call_path's suffix.
    ///
    /// The `mod_path` is significant here as we assume the resolution is done within the
    /// context of the module pointed to by `mod_path` and will only check the call path prefixes
    /// and the symbol's own visibility
    pub(crate) fn resolve_call_path_with_visibility_check(
        &self,
        handler: &Handler,
        engines: &Engines,
        mod_path: &Path,
        call_path: &CallPath,
    ) -> Result<ty::TyDecl, ErrorEmitted> {
        self.resolve_call_path_with_self_with_visibility_check(
            handler, engines, mod_path, call_path, None,
        )
    }

    /// Resolve a symbol that is potentially prefixed with some path, e.g. `foo::bar::symbol`.
    ///
    /// This will concatenate the `mod_path` with the `call_path`'s prefixes and
    /// then calling `resolve_symbol` with the resulting path and call_path's suffix.
    ///
    /// The `mod_path` is significant here as we assume the resolution is done within the
    /// context of the module pointed to by `mod_path` and will only check the call path prefixes
    /// and the symbol's own visibility
    pub(crate) fn resolve_call_path_with_self_with_visibility_check(
        &self,
        handler: &Handler,
        engines: &Engines,
        mod_path: &Path,
        call_path: &CallPath,
        self_type: Option<TypeId>,
    ) -> Result<ty::TyDecl, ErrorEmitted> {
        let (decl, mod_path) =
            self.resolve_call_path_and_mod_path(handler, engines, mod_path, call_path, self_type)?;

        // In case there are no prefixes we don't need to check visibility
        if mod_path.is_empty() {
            return Ok(decl);
        }

        // check the visibility of the call path elements
        // we don't check the first prefix because direct children are always accessible
        for prefix in iter_prefixes(&mod_path).skip(1) {
            let module = self.check_submodule(handler, prefix)?;
            if module.visibility.is_private() {
                let prefix_last = prefix[prefix.len() - 1].clone();
                handler.emit_err(CompileError::ImportPrivateModule {
                    span: prefix_last.span(),
                    name: prefix_last,
                });
            }
        }

        // check the visibility of the symbol itself
        if !decl.visibility(engines.de()).is_public() {
            handler.emit_err(CompileError::ImportPrivateSymbol {
                name: call_path.suffix.clone(),
                span: call_path.suffix.span(),
            });
        }

        Ok(decl)
    }

    /// Given a path to a module and the identifier of a symbol within that module, resolve its
    /// declaration.
    ///
    /// If the symbol is within the given module's namespace via import, we recursively traverse
    /// imports until we find the original declaration.
    pub(crate) fn resolve_symbol(
        &self,
        handler: &Handler,
        engines: &Engines,
        mod_path: &Path,
        symbol: &Ident,
    ) -> Result<ty::TyDecl, ErrorEmitted> {
        let (decl, _) =
            self.resolve_symbol_and_mod_path(handler, engines, mod_path, symbol, None)?;
        Ok(decl)
    }

    fn resolve_symbol_and_mod_path(
        &self,
        handler: &Handler,
        engines: &Engines,
        mod_path: &Path,
        symbol: &Ident,
        self_type: Option<TypeId>,
    ) -> Result<(ty::TyDecl, Vec<Ident>), ErrorEmitted> {
        // This block tries to resolve associated types
        let mut module = &self.module;
        let mut current_mod_path = vec![];
        let mut decl_opt = None;
        let mut type_id_opt = None;
        for (ident_index, ident) in mod_path.iter().enumerate() {
            if let Some(type_id) = type_id_opt {
                type_id_opt = None;
                decl_opt = Some(
                    self.resolve_associated_type_from_type_id(handler, engines, ident, type_id)?,
                );
            } else if ident_index == 0 && ident.as_str() == "Self" {
                if let Some(self_type) = self_type {
                    type_id_opt = Some(self_type);
                } else {
                    return Err(handler.emit_err(CompileError::Internal(
                        "Self type not specified",
                        ident.span(),
                    )));
                }
            } else {
                if let Some(decl) = decl_opt {
                    decl_opt = Some(self.resolve_associated_type(handler, engines, ident, decl)?);
                } else {
                    match module.submodules.get(ident.as_str()) {
                        Some(ns) => {
                            module = ns;
                            current_mod_path.push(ident.clone());
                        }
                        None => {
                            decl_opt = Some(self.resolve_symbol_helper(
                                handler,
                                engines,
                                &current_mod_path,
                                ident,
                                module,
                            )?);
                        }
                    }
                }
            }
        }
        if let Some(type_id) = type_id_opt {
            let decl =
                self.resolve_associated_type_from_type_id(handler, engines, symbol, type_id)?;
            return Ok((decl, current_mod_path));
        }
        if let Some(decl) = decl_opt {
            let decl = self.resolve_associated_type(handler, engines, symbol, decl)?;
            return Ok((decl, current_mod_path));
        }

        self.check_submodule(handler, mod_path).and_then(|module| {
            let decl = self.resolve_symbol_helper(handler, engines, mod_path, symbol, module)?;
            Ok((decl, mod_path.to_vec()))
        })
    }

    fn resolve_associated_type(
        &self,
        handler: &Handler,
        engines: &Engines,
        symbol: &Ident,
        decl: ty::TyDecl,
    ) -> Result<ty::TyDecl, ErrorEmitted> {
        let type_info = match decl.clone() {
            ty::TyDecl::StructDecl(struct_decl) => TypeInfo::Struct(DeclRef::new(
                struct_decl.name.clone(),
                struct_decl.decl_id,
                struct_decl.name.span(),
            )),
            ty::TyDecl::EnumDecl(enum_decl) => TypeInfo::Enum(DeclRef::new(
                enum_decl.name.clone(),
                enum_decl.decl_id,
                enum_decl.name.span(),
            )),
            ty::TyDecl::TypeDecl(type_decl) => {
                let type_decl = engines.de().get_type(&type_decl.decl_id);
                engines.te().get(type_decl.ty.unwrap().type_id)
            }
            _ => {
                return Err(handler.emit_err(CompileError::SymbolNotFound {
                    name: symbol.clone(),
                    span: symbol.span(),
                }))
            }
        };

        self.resolve_associated_type_from_type_id(
            handler,
            engines,
            symbol,
            engines.te().insert(engines, type_info),
        )
    }

    fn resolve_associated_type_from_type_id(
        &self,
        handler: &Handler,
        engines: &Engines,
        symbol: &Ident,
        type_id: TypeId,
    ) -> Result<ty::TyDecl, ErrorEmitted> {
        for trait_item in self.implemented_traits.get_items_for_type(engines, type_id) {
            match trait_item {
                ty::TyTraitItem::Fn(_) => {}
                ty::TyTraitItem::Constant(_) => {}
                ty::TyTraitItem::Type(type_ref) => {
                    let type_decl = engines.de().get_type(type_ref.id());
                    if type_decl.name.as_str() == symbol.as_str() {
                        return Ok(ty::TyDecl::TypeDecl(TypeDecl {
                            name: type_decl.name.clone(),
                            decl_id: *type_ref.id(),
                            decl_span: type_decl.name.span(),
                        }));
                    }
                }
            }
        }

        Err(handler.emit_err(CompileError::SymbolNotFound {
            name: symbol.clone(),
            span: symbol.span(),
        }))
    }

    fn resolve_symbol_helper(
        &self,
        handler: &Handler,
        engines: &Engines,
        mod_path: &Path,
        symbol: &Ident,
        module: &Module,
    ) -> Result<ty::TyDecl, ErrorEmitted> {
        let true_symbol = self[mod_path]
            .use_aliases
            .get(symbol.as_str())
            .unwrap_or(symbol);
        match module.use_synonyms.get(symbol) {
            Some((_, _, decl @ ty::TyDecl::EnumVariantDecl { .. }, _)) => Ok(decl.clone()),
            Some((src_path, _, _, _)) if mod_path != src_path => {
                // TODO: check that the symbol import is public?
                self.resolve_symbol(handler, engines, src_path, true_symbol)
            }
            _ => module
                .check_symbol(true_symbol)
                .map_err(|e| handler.emit_err(e))
                .cloned(),
        }
    }
}

impl std::ops::Deref for Root {
    type Target = Module;
    fn deref(&self) -> &Self::Target {
        &self.module
    }
}

impl std::ops::DerefMut for Root {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.module
    }
}

impl From<Module> for Root {
    fn from(module: Module) -> Self {
        Root { module }
    }
}

impl From<Namespace> for Root {
    fn from(namespace: Namespace) -> Self {
        namespace.root
    }
}
