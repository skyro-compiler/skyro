module Main
import Starknet
%language ElabReflection

deployCompile : External m => (classHash: Felt) -> (contractAddressSalt: Felt) -> (constructorCalldata: Segment) -> (deployFromZero: Felt) -> m Felt
deployCompile = deploy

callContractCompile : External m => (contractAddress: Felt) -> (functionSelector: Felt) -> (calldata: Segment) -> m Segment
callContractCompile = callContract

libraryCallCompile : External m => (classHash: Felt) -> (functionSelector: Felt) -> (calldata: Segment) -> m Segment
libraryCallCompile = libraryCall

libraryCallL1HandlerCompile : External m => (classHash: Felt) -> (functionSelector: Felt) -> (calldata: Segment) -> m Segment
libraryCallL1HandlerCompile = libraryCallL1Handler

main = abi {functions = ["deployCompile", "callContractCompile", "libraryCallCompile", "libraryCallL1HandlerCompile"]} 
