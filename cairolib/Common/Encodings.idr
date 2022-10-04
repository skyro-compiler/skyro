module Common.Encodings

import Common.Segment
import Common.Casts
import Data.Vect
import Common.ECDSA
import Common.Felt

public export
interface Codable a where
  size : Maybe Felt -- Nothing means Unknown
  encode : a -> (1 _:SegmentBuilder) -> SegmentBuilder
  decode : Segment -> Maybe (a, Segment)
  unsafeDecode : Segment -> (a, Segment)
  unsafeDecode seg = case decode seg of
    Nothing => assert_total $ idris_crash "Illegal segment layout for decoding"
    (Just res) => res

public export
Codable Felt where
  size = Just 1
  encode = append
  decode s = if size s > 0
    then Just $ unsafeDecode s
    else Nothing
  unsafeDecode s = (unsafeHead s, unsafeTail s)

public export
(fc:Codable Felt) => Cast Felt a => LosslessCast a Felt => Codable a where
  size = size @{fc}
  encode v = encode @{fc} (lossless_cast v)
  decode seg = case decode @{fc} seg of
    Nothing => Nothing
    (Just (v,seg2)) => Just (cast v, seg2)
  unsafeDecode seg = let (v,seg2) = unsafeDecode @{fc} seg in (cast v, seg2)

public export
Codable Segment where
  size = Nothing
  encode s builder = case head s of
    Nothing => builder
    (Just v) => case tail s of
        Nothing => append v builder
        (Just t) => encode t (append v builder)
  decode seg = do
    l <- head seg
    s2 <- tail seg
    res <- take l s2
    rem <- drop l s2
    pure (res,rem)
  unsafeDecode seg = let (l,seg2) = (unsafeHead seg, unsafeTail seg) in (unsafeTake l seg2, unsafeDrop l seg2)

public export
(ca:Codable a) => (cb:Codable b) => Codable (a,b) where
  size = case (size @{ca}, size @{cb}) of
    (Just as, Just bs) => Just (as + bs)
    _ => Nothing
  encode (av,bv) builder = encode bv (encode av builder)
  decode s = do
    (av,s2) <- decode @{ca} s
    (bv,s3) <- decode @{cb} s2
    pure ((av,bv),s3)
  unsafeDecode s = let (av,s2) = unsafeDecode @{ca} s in
    let (bv,s3) = unsafeDecode @{cb} s2 in ((av,bv),s3)

public export
(ca:Codable a) => Codable (Maybe a) where
  size = Nothing
  encode Nothing builder = append 0 builder
  encode (Just av) builder = encode av (append 1 builder)
  decode seg = do
    l <- head seg
    s2 <- tail seg
    if  l == 0 then pure (Nothing, s2) else do
    (av, rem) <- decode @{ca} s2
    pure (Just av, rem)
  unsafeDecode seg = let (l,seg2) = (unsafeHead seg, unsafeTail seg) in if l == 0
    then (Nothing, seg2)
    else let (av,seg3) = unsafeDecode @{ca} seg2 in (Just av,seg3)

-- helper for the List Codable
produceN : Felt -> (b -> (a,b)) -> b -> (List a, b)
produceN rem f state = if rem <= 0
    then (Nil, state)
    else let (r, nState) = f state in
         let (res, remState) = produceN (rem - 1) f nState in
         (r::res, remState)

produceNMaybe : Felt -> (b -> Maybe (a,b)) -> b -> Maybe (List a, b)
produceNMaybe rem f state = if rem <= 0
    then Just (Nil, state)
    else case f state of
        Nothing => Nothing
        Just (r, nState) => case produceNMaybe (rem - 1) f nState of
            Nothing => Nothing
            Just (res, remState) => Just (r::res, remState)

builderFold : (a -> (1 _: SegmentBuilder) -> SegmentBuilder) -> (1 _: SegmentBuilder) -> List a -> SegmentBuilder
builderFold _ builder Nil = builder
builderFold f builder (x::xs) = builderFold f (f x builder) xs

public export
(ca:Codable a) => Codable (List a) where
    size = Nothing
    encode ls builder = builderFold encode (append (cast $ length ls) builder) ls
    decode seg = do
        l <- head seg
        rem <- tail seg
        produceNMaybe l (decode @{ca}) rem
    unsafeDecode seg = produceN (unsafeHead seg) (unsafeDecode @{ca}) (unsafeTail seg)


-- This is a non-monadic version of createSegmentBuilder that is save if it is ok to reuse SegmentBuilder if a is the same
-- Same reasoning as for unsafeCreateSegmentBuilderForList
%foreign
    "apStable:True"
    "imports:starkware.cairo.common.alloc alloc"
    """
    code:
    func $name$(unusedType, unusedVal) -> (builder):
        let (segPtr) = alloc()
        tempvar builder = new (0, segPtr)
        return (cast(builder,felt))
    end
    """
unsafeCreateSegmentEncoder : a -> SegmentBuilder

-- This allows to use encoder outside of a Cairo Monad in case it will be immediately frozen
export
segmentEncode : Codable a => a -> Segment
segmentEncode v = freeze $ encode v (unsafeCreateSegmentEncoder v)
