module Starknet

-- Copied from official Prelude and excluded PrimIO and IO
import public Builtin
-- import public PrimIO
import public Prelude.Basics as Prelude
import public Prelude.Cast as Prelude
import public Prelude.EqOrd as Prelude
import public Prelude.Interfaces as Prelude
import public Prelude.Interpolation as Prelude
-- import public Prelude.IO as Prelude
import public Prelude.Num as Prelude
import public Prelude.Ops as Prelude
import public Prelude.Show as Prelude
import public Prelude.Types as Prelude
import public Prelude.Uninhabited as Prelude

import public Common
import public Common.Casts
import public Common.Pedersen
import public Common.Felt
import public Common.Dict
import public Common.Memory
import public Common.Segment
import public Common.Encodings

import public Starknet.Types
import public Starknet.Storage
import public Starknet.Events
import public Starknet.Syscall
import public Starknet.Integration.ABI

import Data.Maybe

------------------------------------------------------
-- Implementation of the StarkNet interfaces 
-- `View`, `External`, `Constructor` and `L1Handler`
------------------------------------------------------

public export %inline
View Cairo where
  readStorage = readStorageHelper
  getBlockNumber = getBlockNumberHelper
  getBlockTimestamp = getBlockTimestampHelper
  getCallerAddress = getCallerAddressHelper
  getContractAddress = getContractAddressHelper
  getSequencerAddress = getSequencerAddressHelper


public export %inline
External Cairo where
  writeStorage = writeStorageHelper
  writeEvent = emitEventHelper
  deploy = deployHelper
  callContract = callContractHelper
  libraryCall = libraryCallHelper
  libraryCallL1Handler = libraryCallL1HandlerHelper

public export %inline
Constructor Cairo where 

public export %inline
L1Handler Cairo where 

----------------------------------------------------------------- 
-- Entry point generator code
----------------------------------------------------------------

export
unsafePerformIO : String -> String
unsafePerformIO s = s
