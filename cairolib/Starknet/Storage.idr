module Starknet.Storage

import Data.Maybe

import Common
import Common.Encodings
import Common.Segment

import Starknet.Types
import Starknet.Syscall


-- https://github.com/starkware-libs/cairo-lang/blob/master/src/starkware/starknet/common/syscalls.cairo

export
%foreign 
    "imports:starkware.starknet.common.storage normalize_address"
    "linear_implicits:range_check_ptr"
    """
    code:
    func Starknet_Storage_normalizeAddress(range_check_ptr,address) -> (result, range_check_ptr):
        let (res) = normalize_address{range_check_ptr = range_check_ptr}(address)
        return (res, range_check_ptr)
    end
    """
normalizeAddress : (address: Felt) -> (Felt)

-- This should be consistent to https://docs.starknet.io/docs/Contracts/contract-storage#storage-variables
export
%foreign 
    "linear_implicits:pedersen_ptr"
    """
    code:
    func Starknet_Storage_computeAddress(pedersen_ptr,address, seg) -> (result, pedersen_ptr):
        let len = [seg]
        let ptr = [seg+1]
        if len == 0:
          return (address, pedersen_ptr)
        else:
          assert [pedersen_ptr] = address
          assert [pedersen_ptr + 1] = [ptr]
          return Starknet_Storage_computeAddress(pedersen_ptr + 3, [pedersen_ptr + 2], cast(new (len-1, ptr+1),felt) )
        end
    end
    """
computeAddress : (address: Felt) -> (seg: Segment) -> (Felt)


%foreign 
    "imports:starkware.starknet.common.syscalls storage_read"
    "untupled:(_,_)"
    """
    code:
    func Starknet_Storage_storageReadPrimHelper(address, len, result, syscall_ptr) -> (syscall_ptr):
        if len == 0:
            return (syscall_ptr)
        end

        let syscall_ptr_ = cast(syscall_ptr, felt*)
        let (res) = storage_read{syscall_ptr=syscall_ptr_}(address)
        assert [result] = res
        return Starknet_Storage_storageReadPrimHelper(
            address + 1, len - 1,  cast(result + 1, felt), cast(syscall_ptr_, felt)
        )
    end

    func Starknet_Storage_storageReadPrim(hasStaticSize, address, len, syscall_ptr) -> (
        syscall_ptr, result
    ):  
        alloc_locals
        let (result_ptr) = alloc()
        local result = cast(result_ptr, felt)
        if hasStaticSize == 1:
            let (syscall_ptr) = Starknet_Storage_storageReadPrimHelper(address, len, result, syscall_ptr)
            return (syscall_ptr, cast(new (len, result), felt))
        else:
            let syscall_ptr_ = cast(syscall_ptr, felt*)
            let (len) = storage_read{syscall_ptr=syscall_ptr_}(address)
            let (syscall_ptr) = Starknet_Storage_storageReadPrimHelper(address + 1, len, result, syscall_ptr)
            return (syscall_ptr, cast(new (len, result), felt))
        end
    end
    """
storageReadPrim : (hasStaticSize: Bool) -> (address: Felt) ->  (len: Felt) -> PrimCairo Segment

public export %inline 
rawStorageRead : (hasStaticSize: Bool) -> (address: Felt) ->  (len: Felt) -> Cairo Segment
rawStorageRead hasStaticSize address len = fromPrimCairo (storageReadPrim hasStaticSize address len)

public export %inline 
readStorageHelper : (c: Codable e) => (addr: StorageAddress) -> Cairo e
readStorageHelper (MkStorageAddr address) = case size @{c} of
    Just nrElems => map (fst . decode) $ rawStorageRead True address (cast nrElems)
    Nothing      => map (fst . decode) $ rawStorageRead False address 0
 


%foreign 
    "imports:starkware.starknet.common.syscalls storage_write"
    """
    code:
    func Starknet_Storage_storageWritePrimHelper(address, len, ptr, syscall_ptr) -> (syscall_ptr):
        if len == 0:
            return (syscall_ptr)
        end

        let syscall_ptr_ = cast(syscall_ptr, felt*)
        storage_write{syscall_ptr = syscall_ptr_}(address,[ptr])
        return Starknet_Storage_storageWritePrimHelper(address + 1, len-1, ptr + 1, cast(syscall_ptr_, felt))
    end


    func Starknet_Storage_storageWritePrim(hasStaticSize, address, seg, syscall_ptr) -> (syscall_ptr):
        if hasStaticSize == 1:
            let (syscall_ptr) = Starknet_Storage_storageWritePrimHelper(address, [seg], [seg+1], syscall_ptr)
        else:
            let syscall_ptr_ = cast(syscall_ptr, felt*)
            storage_write{syscall_ptr = syscall_ptr_}(address,[seg])
            let syscall_ptr = cast(syscall_ptr_, felt)
            let (syscall_ptr) = Starknet_Storage_storageWritePrimHelper(address+1, [seg], [seg+1], syscall_ptr)
        end
        return (syscall_ptr)
    end
    """
storageWritePrim : (hasStaticSize: Bool) -> (address: Felt) ->  (seg: Segment) -> PrimCairoUnit

public export %inline 
rawStorageWrite : Bool -> Felt -> Segment -> Cairo ()
rawStorageWrite hasStaticSize address seg = fromPrimCairoUnit (storageWritePrim hasStaticSize address seg)

public export %inline 
writeStorageHelper : (c: Codable e) => (addr: StorageAddress) -> (value: e) -> Cairo Unit
writeStorageHelper {c} (MkStorageAddr address) val = 
    let staticSize = isJust (size @{c})
     in rawStorageWrite staticSize address (encode val)



-- Higher level API
public export
data StorageSpace : (params: List Type) -> (result: Type)-> Type where
  MkStorageSpace : (addr: Felt) -> StorageSpace params result

public export
StorageSlot : Type -> Type
StorageSlot = StorageSpace []

public export %inline
readStorageVar : View m => Codable e => StorageSlot e -> m e
readStorageVar (MkStorageSpace addr) = readStorage (MkStorageAddr addr)
 
public export %inline
writeStorageVar : External m => Codable e => StorageSlot e -> e -> m ()
writeStorageVar (MkStorageSpace addr) val = writeStorage (MkStorageAddr addr) val

public export %inline
at : Codable p => {ps: List Type} -> StorageSpace (p::ps) r -> p -> (StorageSpace ps r)
at {ps=[]} (MkStorageSpace addr) p = 
  let seg = encode p
   in MkStorageSpace (normalizeAddress $ computeAddress addr seg)
at {ps=_} (MkStorageSpace addr) p = 
  let seg = encode p
   in MkStorageSpace (computeAddress addr seg)