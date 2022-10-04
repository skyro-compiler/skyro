import os
import pytest

from starkware.starknet.testing.starknet import Starknet
from starkware.starknet.public.abi import get_selector_from_name
from starkware.starknet.business_logic.execution.objects import Event

# The path to the contract source code.
CONTRACT_FILE = os.path.join(
    os.path.dirname(__file__), "build/exec/Main.cairo")

caller_address = 123456789

@pytest.mark.asyncio
async def test_view():
    starknet = await Starknet.empty()

    contract = await starknet.deploy(
        source=CONTRACT_FILE,
        cairo_path = ["../../../../skyro-runtime"],
        constructor_calldata=[]
    )

    writeResult = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("changeBalance"),
        calldata=[42],
        caller_address = caller_address,
        max_fee = 0
    )

    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("getBalance"),
        calldata=[caller_address],
        caller_address = caller_address,
        max_fee = 0
    )

    assert result.call_info.retdata == [42]

    (actual_raw_event,) = writeResult.get_sorted_events()


    assert actual_raw_event == Event(
        from_address=contract.contract_address,
        keys=[get_selector_from_name("balanceChanged")],
        data=[caller_address,42],
    )
