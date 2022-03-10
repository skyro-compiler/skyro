module Starknet.Syscall

import Common
import Common.Memory

-- https://github.com/starkware-libs/cairo-lang/blob/master/src/starkware/starknet/common/syscalls.cairo

export
%foreign 
    "imports:starkware.starknet.common.storage normalize_address"
    "linear_implicits:range_check_ptr"
    """
    code:
    func Starknet_Syscall_normalizeAddress(range_check_ptr,address) -> (result, range_check_ptr):
        let (res) = normalize_address{range_check_ptr = range_check_ptr}(address)
        return (res, range_check_ptr)
    end
    """
normalizeAddress : (address: Felt) -> (Felt)


%foreign 
    "imports:starkware.starknet.common.syscalls storage_read"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_storageReadPrim(address, syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (res) = storage_read{syscall_ptr = syscall_ptr_}(address)
        return (cast(syscall_ptr_, felt), res)
    end
    """
storageReadPrim : (address: Felt) -> PrimCairo Felt

public export %inline 
storageRead : Felt -> Cairo Felt
storageRead address = fromPrimCairo (storageReadPrim address)


%foreign 
    "imports:starkware.starknet.common.syscalls storage_write"
    """
    code:
    func Starknet_Syscall_storageWritePrim(address, value, syscall_ptr) -> (syscall_ptr):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        storage_write{syscall_ptr = syscall_ptr_}(address,value)
        return (cast(syscall_ptr_, felt))
    end
    """
storageWritePrim : (address: Felt) -> (value: Felt) -> PrimCairoUnit

public export %inline 
storageWrite : Felt -> Felt -> Cairo ()
storageWrite address value = fromPrimCairoUnit (storageWritePrim address value)


%foreign 
    "imports:starkware.starknet.common.syscalls emit_event"
    """
    code:
    func Starknet_Syscall_emitEventPrim(keys_len, keys, data_len, data, syscall_ptr) -> (syscall_ptr):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        emit_event{syscall_ptr = syscall_ptr_}(keys_len, cast(keys, felt*), data_len, cast(data, felt*))
        return (cast(syscall_ptr_, felt))
    end
    """
emitEventPrim : Felt -> CairoPtr Memory -> Felt -> CairoPtr Memory -> PrimCairoUnit

public export %inline
emitEvent : Felt -> CairoPtr Memory -> Felt -> CairoPtr Memory -> Cairo () -- keys and data should be felt*
emitEvent keys_len keys data_len data_ = fromPrimCairoUnit (emitEventPrim keys_len keys data_len data_)


%foreign 
    "imports:starkware.starknet.common.syscalls get_block_timestamp"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_getBlockTimestampPrim(syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (result) = get_block_timestamp{syscall_ptr = syscall_ptr_}()
        return (cast(syscall_ptr_, felt), result)
    end
    """
getBlockTimestampPrim : PrimCairo Felt

public export %inline 
getBlockTimestamp : Cairo Felt
getBlockTimestamp = fromPrimCairo getBlockTimestampPrim
