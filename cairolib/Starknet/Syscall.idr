module Starknet.Syscall

import Common
import Common.Segment

-- Readonly functions
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
getBlockTimestampHelper : Cairo Felt
getBlockTimestampHelper = fromPrimCairo getBlockTimestampPrim


%foreign 
    "imports:starkware.starknet.common.syscalls get_block_number"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_getBlockNumberPrim(syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (result) = get_block_number{syscall_ptr = syscall_ptr_}()
        return (cast(syscall_ptr_, felt), result)
    end
    """
getBlockNumberPrim : PrimCairo Felt

public export %inline 
getBlockNumberHelper : Cairo Felt
getBlockNumberHelper = fromPrimCairo getBlockNumberPrim


%foreign 
    "imports:starkware.starknet.common.syscalls get_caller_address"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_getCallerAddressPrim(syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (result) = get_caller_address{syscall_ptr = syscall_ptr_}()
        return (cast(syscall_ptr_, felt), result)
    end
    """
getCallerAddressPrim : PrimCairo Felt

public export %inline 
getCallerAddressHelper : Cairo Felt
getCallerAddressHelper = fromPrimCairo getCallerAddressPrim


%foreign 
    "imports:starkware.starknet.common.syscalls get_contract_address"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_getContractAddressPrim(syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (result) = get_contract_address{syscall_ptr = syscall_ptr_}()
        return (cast(syscall_ptr_, felt), result)
    end
    """
getContractAddressPrim : PrimCairo Felt

public export %inline 
getContractAddressHelper : Cairo Felt
getContractAddressHelper = fromPrimCairo getContractAddressPrim


%foreign 
    "imports:starkware.starknet.common.syscalls get_sequencer_address"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_getSequencerAddressPrim(syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (result) = get_sequencer_address{syscall_ptr = syscall_ptr_}()
        return (cast(syscall_ptr_, felt), result)
    end
    """
getSequencerAddressPrim : PrimCairo Felt

public export %inline 
getSequencerAddressHelper : Cairo Felt
getSequencerAddressHelper = fromPrimCairo getSequencerAddressPrim



-- Modifying functions

%foreign 
    "imports:starkware.starknet.common.syscalls deploy"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_deployPrim(class_hash, contract_address_salt, constructor_calldata, syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (result) = deploy{syscall_ptr = syscall_ptr_}(class_hash, contract_address_salt, [constructor_calldata], cast([constructor_calldata+1],felt*))
        return (cast(syscall_ptr_, felt), result)
    end
    """
deployPrim : Felt -> Felt -> Segment -> PrimCairo Felt 

public export %inline 
deployHelper : Felt -> Felt -> Segment -> Cairo Felt
deployHelper classHash contractAddressSalt constructorCalldata = fromPrimCairo (deployPrim classHash contractAddressSalt constructorCalldata)


%foreign 
    "imports:starkware.starknet.common.syscalls call_contract"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_callContractPrim(contract_address, function_selector, calldata, syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (retdata_size, retdata) = call_contract{syscall_ptr = syscall_ptr_}(contract_address, function_selector, [calldata], cast([calldata+1],felt*))
        return (cast(syscall_ptr_, felt),  cast(new (retdata_size, retdata), felt))
    end
    """
callContractPrim : Felt -> Felt -> Segment -> PrimCairo Segment 

public export %inline 
callContractHelper : Felt -> Felt -> Segment -> Cairo Segment
callContractHelper contractAddress functionSelector calldata = fromPrimCairo (callContractPrim contractAddress functionSelector calldata)


%foreign 
    "imports:starkware.starknet.common.syscalls library_call"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_libraryCallPrim(class_hash, function_selector, calldata, syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (retdata_size, retdata) = library_call{syscall_ptr = syscall_ptr_}(class_hash, function_selector, [calldata], cast([calldata+1],felt*))
        return (cast(syscall_ptr_, felt),  cast(new (retdata_size, retdata), felt))
    end
    """
libraryCallPrim : Felt -> Felt -> Segment -> PrimCairo Segment 

public export %inline 
libraryCallHelper : Felt -> Felt -> Segment -> Cairo Segment
libraryCallHelper classHash functionSelector calldata = fromPrimCairo (libraryCallPrim classHash functionSelector calldata)


%foreign 
    "imports:starkware.starknet.common.syscalls library_call_l1_handler"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Syscall_libraryCallL1HandlerPrim(class_hash, function_selector, calldata, syscall_ptr) -> (syscall_ptr, result):
        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (retdata_size, retdata) = library_call_l1_handler{syscall_ptr = syscall_ptr_}(class_hash, function_selector, [calldata], cast([calldata+1],felt*))
        return (cast(syscall_ptr_, felt),  cast(new (retdata_size, retdata), felt))
    end
    """
libraryCallL1HandlerPrim : Felt -> Felt -> Segment -> PrimCairo Segment 

public export %inline 
libraryCallL1HandlerHelper : Felt -> Felt -> Segment -> Cairo Segment
libraryCallL1HandlerHelper classHash functionSelector calldata = fromPrimCairo (libraryCallL1HandlerPrim classHash functionSelector calldata)