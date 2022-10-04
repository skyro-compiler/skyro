module Starknet.Types

import Common
import Common.Encodings
import Common.Segment

public export
data StorageAddress = MkStorageAddr Felt

public export
data EventData = MkEventData Segment Segment

-- View requires a Monad implementation (to keep constraints list small)
public export
interface Monad m => View m where
  readStorage : Codable e => (addr: StorageAddress) -> m e 
  getBlockNumber : m Felt
  getBlockTimestamp : m Felt
  getCallerAddress : m Felt
  getContractAddress : m Felt
  getSequencerAddress : m Felt


-- External requires a View implementation
public export
interface View m => External m where 
  writeStorage : Codable e => (addr: StorageAddress) -> (value: e) -> m Unit
  writeEvent : EventData -> m Unit
  deploy : (classHash: Felt) -> (contractAddressSalt: Felt) -> (constructorCalldata: Segment) -> (deployFromZero:Felt) -> m Felt
  callContract : (contractAddress: Felt) -> (functionSelector: Felt) -> (calldata: Segment) -> m Segment
  libraryCall : (classHash: Felt) -> (functionSelector: Felt) -> (calldata: Segment) -> m Segment
  libraryCallL1Handler : (classHash: Felt) -> (functionSelector: Felt) -> (calldata: Segment) -> m Segment
   

-- Marker interface for constructors
public export
interface External m => Constructor m where

-- Marker interface for L1 handlers
public export 
interface External m => L1Handler m where
