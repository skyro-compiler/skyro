module Starknet.Events

import Starknet.Types
import Common
import Common.Encodings
import Common.Segment


%foreign 
    "imports:starkware.starknet.common.syscalls emit_event"
    """
    code:
    func Starknet_Events_emitEventPrim(keys, values, syscall_ptr) -> (syscall_ptr):
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
emitEventHelper : EventDesc [] [] -> Cairo Unit
emitEventHelper (MkEventDesc keysS valsS) = rawEmitEvent keysS valsS

export
applyKey : Codable k => EventDesc (k::ks) vals -> k -> EventDesc ks vals
applyKey (MkEventDesc keysS valsS) k = MkEventDesc (keysS ++ encode k) valsS

export
applyValue : Codable v => EventDesc keys (v::vs) -> v -> EventDesc keys vs
applyValue (MkEventDesc keysS valsS) v = MkEventDesc keysS (valsS ++ encode v)
