import os
import pytest

from starkware.starknet.testing.starknet import Starknet
from starkware.starknet.public.abi import get_selector_from_name

# The path to the contract source code.
CONTRACT_FILE = os.path.join(
    os.path.dirname(__file__), "build/exec/Main.cairo")

CONTRACT_FILE_TARGET = os.path.join(
    os.path.dirname(__file__), "build/exec/Contract.cairo")


@pytest.mark.asyncio
async def test_call():
    starknet = await Starknet.empty()

    target = await starknet.deploy(
        source=CONTRACT_FILE_TARGET,
        cairo_path = ["../../../../skyro-runtime"],
        disable_hint_validation = True,
        constructor_calldata=[]
    )

    contract = await starknet.deploy(
        source=CONTRACT_FILE,
        cairo_path = ["../../../../skyro-runtime"],
        disable_hint_validation = True,
        constructor_calldata=[]
    )

    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("increment"),
        calldata=[target.contract_address],
        caller_address = 0,
        max_fee = 0
    )

    result = await starknet.state.invoke_raw(
        contract_address=contract.contract_address,
        selector=get_selector_from_name("increment"),
        calldata=[target.contract_address],
        caller_address = 0,
        max_fee = 0
    )

    result = await starknet.state.invoke_raw(
        contract_address=target.contract_address,
        selector=get_selector_from_name("get"),
        calldata=[1],
        caller_address = 0,
        max_fee = 0
    )

    assert result.call_info.retdata == [2]
