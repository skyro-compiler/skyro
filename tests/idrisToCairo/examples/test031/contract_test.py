import os
import pytest

from starkware.starknet.testing.starknet import Starknet

# The path to the contract source code.
CONTRACT_FILE = os.path.join(
    os.path.dirname(__file__), "build/exec/Main.cairo")


@pytest.mark.asyncio
async def test_call():
    starknet = await Starknet.empty()

    contract = await starknet.deploy(
        source=CONTRACT_FILE,
        cairo_path = ["../../../../skyro-runtime"],
        disable_hint_validation = True,
        constructor_calldata=[]
    )
