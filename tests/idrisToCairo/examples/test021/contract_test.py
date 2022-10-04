import os
import pytest

from starkware.starknet.testing.starknet import Starknet
from starkware.starknet.public.abi import get_selector_from_name

# The path to the contract source code.
CONTRACT_FILE = os.path.join(
    os.path.dirname(__file__), "build/exec/Main.cairo")


@pytest.mark.asyncio
async def test_view():
    starknet = await Starknet.empty()

    contract = await starknet.deploy(
        source=CONTRACT_FILE,
        cairo_path = ["../../../../skyro-runtime"],
        constructor_calldata=[]
    )
 
    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("eval"),
        calldata=[0,1,1,1,2],
        caller_address = 0,
        max_fee = 0
    )

    assert result.call_info.retdata == [3]
