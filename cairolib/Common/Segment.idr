module Common.Segment

import Common
import Common.Memory

export
data Segment: Type where [external]

export
data SegmentBuilder : Type where
  MkSegmentBuilder : (1 _:Segment) -> SegmentBuilder

%foreign 
    "apStable:True"
    "untupled:(_,_)"
    "imports:starkware.cairo.common.alloc alloc"
    """
    code:
    func $name$(world) -> (world, builder):
        let (segPtr) = alloc()
        tempvar builder = new (0, segPtr)
        return (world, cast(builder,felt))
    end
    """
createSegmentBuilderPrim : PrimCairo SegmentBuilder

public export %inline
createSegmentBuilder : Cairo SegmentBuilder
createSegmentBuilder = fromPrimCairo createSegmentBuilderPrim

export
%foreign 
    """
    code:
    func $name$(value, builder) -> (builder):
       let segment = [builder+1]
       let size = [builder]
       assert [segment + size] = value # Append value
       
       tempvar newBuilder = new (size + 1, segment)     
       return (cast(newBuilder, felt))
    end
    """
append : (value : Felt) -> (1 builder: SegmentBuilder) -> SegmentBuilder

export
freeze : SegmentBuilder -> Segment
freeze (MkSegmentBuilder segment) = segment

export
%foreign 
    """
    code:
    func $name$(index, segment) -> (result):
       return ([[segment+1]+index])
    end
    """
index : Felt -> Segment -> Felt

export
%foreign 
    """
    code:
    func $name$(segment) -> (result):
       return ([segment])
    end
    """
size : Segment -> Felt

export
%foreign 
    """
    code:
    func $name$(segment) -> (result):
       return ([segment+1])
    end
    """
mem : Segment -> CairoPtr Memory

export
%foreign
    """
    code:
    func $name$(amount,segment) -> (result):
       let segment = [segment+1]
       tempvar newSegment = new (amount, segment)
       return (cast(newSegment, felt))
    end
    """
unsafeTake : Felt -> Segment -> Segment

export
take : Felt -> Segment -> Maybe Segment
take amount segment =
  if size segment > amount
    then Nothing
    else Just $ unsafeTake amount segment

export
%foreign
    """
    code:
    func $name$(amount,segment) -> (result):
       let segment = [segment+1]
       let size = [segment]
       tempvar newSegment = new (size - amount, segment + amount)
       return (cast(newSegment, felt))
    end
    """
unsafeDrop : Felt -> Segment -> Segment

export
drop : Felt -> Segment -> Maybe Segment
drop amount segment =
  if size segment > amount
    then Nothing
    else Just $ unsafeDrop amount segment

export
%foreign 
    """
    code:
    func $name$(segment) -> (result):
        if [segment] == 0:
            assert 1 = 0
        end
       return ([[segment+1]])
    end
    """
unsafeHead : Segment -> Felt

export
head : Segment -> Maybe Felt
head segment = 
  if size segment == 0 
    then Nothing
    else Just (unsafeHead segment)

export
%foreign 
    """
    code:
    func $name$(segment) -> (result):
        if [segment] == 0:
            assert 1 = 0
        end
        tempvar tail = new ([segment]-1, [segment+1]+1)
        return (cast(tail, felt))
    end
    """
unsafeTail : Segment -> Segment

export
tail : Segment -> Maybe Segment
tail segment = 
  if size segment == 0 
    then Nothing
    else Just (unsafeTail segment)

public export
%foreign 
    "apStable:True"
    "imports:starkware.cairo.common.alloc alloc"
    """
    code:
    func $name$(value) -> (segment):
        let (segPtr) = alloc()
        assert [segPtr] = value
        tempvar builder = new (1, segPtr)
        return (cast(builder,felt))
    end
    """
singletonSegment : Felt -> Segment

public export
%foreign 
    "apStable:True"
    """
    code:
    func $name$() -> (segment):
        tempvar builder = new (0, 0)
        return (cast(builder,felt))
    end
    """
emptySegment : Segment


-- todo: is this save (I do not think so)
-- export
-- listToSegment : List Felt -> Segment
-- listToSegment list = freeze (buildSegment list unsafeCreateSegmentBuilder)
--     where buildSegment : List Felt -> SegmentBuilder -> SegmentBuilder
--           buildSegment []      builder = builder
--           buildSegment (f::fs) builder = buildSegment fs (append f builder)

---------- Skyro Code but with Idris Syntax (so no linearity etc) -------
-- let a = listToSegment [1,2]
-- let b = listToSegment [3,4]
---------- Inline -----------------
-- let a = freeze (buildSegment [1,2] unsafeCreateSegmentBuilder)
-- let b = freeze (buildSegment [3,4] unsafeCreateSegmentBuilder)
---------- Deduplication ----------
-- let shared = unsafeCreateSegmentBuilder
-- let a = freeze (buildSegment [1,2] shared)
-- let b = freeze (buildSegment [3,4] shared) -- will throw error as it tries to overwrite 1
-----------------------------------

-- Option 1: Make Copy On Write Segment -- needs Hints
-- Option 2: Make listToSegment in Cairo Code -- requires knowledge about List representation
-- Option 3: Make an abstraction that builds the segment based on the input

-- Used Option 3
--  This works as if the list is the same its save to return the same SegmentBuilder
--   because Skyro will write the same Felt values at the same position and as writing = asserting it works
%foreign
    "apStable:True"
    "imports:starkware.cairo.common.alloc alloc"
    """
    code:
    func $name$(unused) -> (builder):
        let (segPtr) = alloc()
        tempvar builder = new (0, segPtr)
        return (cast(builder,felt))
    end
    """
unsafeCreateSegmentBuilderForList : List Felt -> SegmentBuilder

export
listToSegment : List Felt -> Segment
listToSegment list = freeze (buildSegment list (unsafeCreateSegmentBuilderForList list))
  where buildSegment : List Felt -> SegmentBuilder -> SegmentBuilder
        buildSegment []      builder = builder
        buildSegment (f::fs) builder = buildSegment fs (append f builder)

export
segmentToList : Segment -> List Felt
segmentToList segment = buildList 0
  where segSize : Felt
        segSize = size segment
        buildList : Felt -> List Felt
        buildList n = 
          if n == segSize 
            then [] 
            else index n segment :: buildList (n+1)


public export
%foreign 
    "apStable:True"
    "imports:starkware.cairo.common.alloc alloc, starkware.cairo.common.memcpy memcpy"
    """
    code:
    func $name$(xs, ys) -> (res):
        alloc_locals
        let (local segPtr) = alloc()
        let sizeX = [xs]
        let sizeY = [ys]
        memcpy(segPtr, cast([xs+1],felt*), sizeX)
        memcpy(segPtr + sizeX, cast([ys + 1],felt*), sizeY)
        tempvar builder = new (sizeX + sizeY, segPtr)
        return (cast(builder,felt))
    end
    """
concat : Segment -> Segment -> Segment

public export %inline
(++) : Segment -> Segment -> Segment
(++) = concat



