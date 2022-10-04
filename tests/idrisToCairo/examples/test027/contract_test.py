import os
import pytest

from starkware.starknet.testing.starknet import Starknet
from starkware.starknet.public.abi import get_selector_from_name
from starkware.cairo.lang.cairo_constants import DEFAULT_PRIME as PRIME

# The path to the contract source code.
CONTRACT_FILE = os.path.join(
    os.path.dirname(__file__), "build/exec/Main.cairo")

@pytest.mark.asyncio
async def test_view():
    starknet = await Starknet.empty()

    contract = await starknet.deploy(
        source=CONTRACT_FILE,
        cairo_path = ["../../../../skyro-runtime"],
        disable_hint_validation = True,
        constructor_calldata=[]
    )

    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("viewSegEx"),
        calldata=[4,0,1,2,3],
        caller_address = 0,
        max_fee = 0
    )

    assert result.call_info.retdata == [4,0,1,2,3]

    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("viewNatEx"),
        calldata=[1,3,0,1,2],
        caller_address = 0,
        max_fee = 0
    )

    assert result.call_info.retdata == [1,3,1,1,2]


    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("viewIntegerEx"),
        calldata=[1,3,10,1,2],
        caller_address = 0,
        max_fee = 0
    )

    assert result.call_info.retdata == [1,3,15,1,2]

    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("viewIntegerEx"),
        calldata=[(-1 % PRIME),3,10,1,2],
        caller_address = 0,
        max_fee = 0
    )

    assert result.call_info.retdata == [(-1 % PRIME),3,5,1,2]

    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("viewNatEx"),
        calldata=[(-1 % PRIME),3,1,1,2],
        caller_address = 0,
        max_fee = 0
    )

    assert result.call_info.retdata == [(-1 % PRIME),3,0,1,2]
