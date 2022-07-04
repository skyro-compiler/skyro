import os
import pytest

from starkware.starknet.testing.starknet import Starknet
from starkware.starknet.public.abi import get_selector_from_name
from starkware.starknet.business_logic.execution.objects import Event

# The path to the contract source code.
CONTRACT_FILE = os.path.join(
    os.path.dirname(__file__), "build/exec/Main.cairo")


@pytest.mark.asyncio
async def test_view():
    starknet = await Starknet.empty()
    contract = await starknet.deploy(
        source=CONTRACT_FILE
    )


    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("blockNumber"),
        calldata=[],
        caller_address = 0,
        max_fee = 0
    )
 

    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("blockTimestamp"),
        calldata=[],
        caller_address = 0,
        max_fee = 0
    )


    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("callerAddress"),
        calldata=[],
        caller_address = 12345,
        max_fee = 0
    )

    assert result.call_info.retdata == [12345]


    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("contractAddress"),
        calldata=[],
        caller_address = 0,
        max_fee = 0
    )

    assert result.call_info.retdata == [contract.contract_address]


    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("sequencerAddress"),
        calldata=[],
        caller_address = 0,
        max_fee = 0
    )