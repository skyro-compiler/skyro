module Main
import Starknet
%language ElabReflection

blockNumber : View m => m Felt
blockNumber = getBlockNumber

blockTimestamp : View m => m Felt
blockTimestamp = getBlockTimestamp

callerAddress : View m => m Felt
callerAddress = getCallerAddress

contractAddress : View m => m Felt
contractAddress = getContractAddress

sequencerAddress : View m => m Felt
sequencerAddress = getSequencerAddress


main = abi {functions = ["blockNumber", "blockTimestamp", "callerAddress", "contractAddress", "sequencerAddress"]} 
