module Common.Memory
import Common

export
data CairoPtr : Type -> Type where [external]

export
data Memory : Type where [external]

%foreign 
    "apStable:True"
    "untupled:(_,_)"
    "imports:starkware.cairo.common.alloc alloc"
    """
    code:
    func $name$(world) -> (world, res):
        let (mem) = alloc()
        return (world, cast(mem,felt))
    end
    """
createMemoryPrim : PrimCairo (CairoPtr Memory)

public export %inline
createMemory : Cairo (CairoPtr Memory)
createMemory = fromPrimCairo createMemoryPrim


%foreign 
    "apStable:True"
    """
    code:
    func $name$(offset, value, ptr, world) -> (world):
        assert [ptr+offset] = value
        return (world)
    end
    """
writeMemoryPrim : (offset:Felt) -> (value: Felt) -> (CairoPtr Memory) -> PrimCairoUnit

public export %inline
writeMemory : Felt -> Felt -> (CairoPtr Memory) -> Cairo ()
writeMemory offset value ptr = fromPrimCairoUnit $ writeMemoryPrim offset value ptr


%foreign 
    "apStable:True"
    "untupled:(_,_)"
    """
    code:
    func $name$(offset, ptr, world) -> (world,res):
        let res = [ptr+offset]
        return (world, res)
    end
    """
readMemoryPrim : (offset:Felt) -> (CairoPtr Memory) -> PrimCairo Felt

public export  %inline
readMemory : Felt -> (CairoPtr Memory) -> Cairo Felt
readMemory offset ptr = fromPrimCairo $ readMemoryPrim offset ptr
