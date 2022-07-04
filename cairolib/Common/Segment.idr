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
    func Common_Segment_createSegmentBuilderPrim(world) -> (world, builder):
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
    func Common_Segment_append(value, builder) -> (builder):
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
    func Common_Segment_index(index, segment) -> (result):
       return ([[segment+1]+index])
    end
    """
index : Felt -> Segment -> Felt

export
%foreign 
    """
    code:
    func Common_Segment_size(segment) -> (result):
       return ([segment])
    end
    """
size : Segment -> Felt

export
%foreign 
    """
    code:
    func Common_Segment_mem(segment) -> (result):
       return ([segment+1])
    end
    """
mem : Segment -> Memory


export
%foreign
    """
    code:
    func Common_Segment_unsafeTake(amount,segment) -> (result):
       let segment = [segment+1]
       tempvar newSegment = new (amount, segment)
       return (cast(newSegment, felt))
    end
    """
unsafeTake : Felt -> Segment -> Segment

export
%foreign
    """
    code:
    func Common_Segment_unsafeDrop(amount,segment) -> (result):
       let segment = [segment+1]
       let size = [segment]
       tempvar newSegment = new (size - amount, segment + amount)
       return (cast(newSegment, felt))
    end
    """
unsafeDrop : Felt -> Segment -> Segment

export
%foreign 
    """
    code:
    func Common_Segment_unsafeHead(segment) -> (result):
        if [segment] == 0:
            assert 1 = 0
        end
       return ([[segment+1]])
    end
    """
unsafeHead : Segment -> Felt

head : Segment -> Maybe Felt
head segment = 
  if size segment == 0 
    then Nothing
    else Just (unsafeHead segment)

export
%foreign 
    """
    code:
    func Common_Segment_unsafeTail(segment) -> (result):
        if [segment] == 0:
            assert 1 = 0
        end
        tempvar tail = new ([segment]-1, [segment+1]+1)
        return (cast(tail, felt))
    end
    """
unsafeTail : Segment -> Segment

tail : Segment -> Maybe Segment
tail segment = 
  if size segment == 0 
    then Nothing
    else Just (unsafeTail segment)


%foreign 
    "apStable:True"
    "imports:starkware.cairo.common.alloc alloc"
    """
    code:
    func Common_Segment_unsafeCreateSegmentBuilder() -> (builder):
        let (segPtr) = alloc()
        tempvar builder = new (0, segPtr)
        return (cast(builder,felt))
    end
    """
unsafeCreateSegmentBuilder : SegmentBuilder

public export
%foreign 
    "apStable:True"
    "imports:starkware.cairo.common.alloc alloc"
    """
    code:
    func Common_Segment_singletonSegment(value) -> (segment):
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
    func Common_Segment_emptySegment() -> (segment):
        tempvar builder = new (0, 0)
        return (cast(builder,felt))
    end
    """
emptySegment : Segment


export
listToSegment : List Felt -> Segment
listToSegment list = freeze (buildSegment list unsafeCreateSegmentBuilder)
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
    func Common_Segment_concat(xs, ys) -> (res):
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