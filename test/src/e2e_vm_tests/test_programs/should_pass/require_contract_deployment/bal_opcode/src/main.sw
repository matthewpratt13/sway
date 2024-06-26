script;

use balance_test_abi::BalanceTest;

#[cfg(experimental_new_encoding = false)]
const CONTRACT_ID = 0x3b8cb681056f61a41e138b8884d7e3bb9332fbd7a8e38e3e0b0ada766cabfa4e;
#[cfg(experimental_new_encoding = true)]
const CONTRACT_ID = 0xd354c2c31bb641863d03eaf320488ae276386ce60ef2e561258efef617dab462;

fn main() -> bool {
    let balance_test_contract = abi(BalanceTest, CONTRACT_ID);
    let number = balance_test_contract.get_42 {
        gas: u64::max()
    }
    ();

    let balance = asm(asset_bal, asset: AssetId::base(), id: CONTRACT_ID) {
        bal asset_bal asset id;
        asset_bal: u64
    };
    assert(balance == 0);
    assert(number == 42);

    true
}
