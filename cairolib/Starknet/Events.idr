module Starknet.Events

import Starknet.Types
import Common
import Common.Encodings
import Common.Segment


%foreign 
    "imports:starkware.starknet.common.syscalls emit_event"
    """
    code:
    func $name$(keys, values, syscall_ptr) -> (syscall_ptr):
        let keys_len = [keys]
        let keys_ptr = cast([keys+1], felt*)
        let values_len = [values]
        let values_ptr = cast([values+1], felt*)

        let syscall_ptr_ = cast(syscall_ptr, felt*)
        emit_event{syscall_ptr = syscall_ptr_}(keys_len, keys_ptr, values_len, values_ptr)
        return (cast(syscall_ptr_, felt))
    end
    """
emitEventPrim : Segment -> Segment -> PrimCairoUnit

public export %inline
rawEmitEvent : Segment -> Segment -> Cairo ()
rawEmitEvent keys values = fromPrimCairoUnit (emitEventPrim keys values)

public export %inline
emitEventHelper : EventData -> Cairo Unit
emitEventHelper (MkEventData keysS valsS) = rawEmitEvent keysS valsS

-- Higher level API
-- allows custom event schemes
public export
interface EventScheme s where
    fromEventId : Felt -> s

public export
data EventDesc : (keys: List Type) -> (values: List Type) -> Type where
  MkEventDesc : Segment -> Segment -> EventDesc keys values

-- default Event Scheme
public export
EventScheme (EventDesc keys values) where
    fromEventId id = MkEventDesc (singletonSegment id) emptySegment

public export %inline
emitEvent : External m => EventDesc [] [] -> m Unit
emitEvent (MkEventDesc keysS valsS) = writeEvent (MkEventData keysS valsS)

export
applyKey : Codable k => EventDesc (k::ks) vals -> k -> EventDesc ks vals
applyKey (MkEventDesc keysS valsS) k = MkEventDesc (keysS ++ segmentEncode k) valsS

export
applyValue : Codable v => EventDesc keys (v::vs) -> v -> EventDesc keys vs
applyValue (MkEventDesc keysS valsS) v = MkEventDesc keysS (valsS ++ segmentEncode v)
