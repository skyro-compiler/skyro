module Common.Encodings

import Common.Segment
import Data.Vect
import Common.ECDSA
import Common.Felt

public export
interface Codable a  where
  size : Maybe Felt -- Nothing means Unknown
  encode : a -> Segment
  decode : Segment -> (a, Segment)

public export
Codable Felt where
  size = Just 1
  encode = singletonSegment
  decode s = (unsafeHead s, unsafeTail s)

-- allows use with other primitives:  we could make Felt generic, however in general casts may not be loss fre
--  as soon as BigInts are implemented this is no longer save
--  Todo: this is just for demonstration purposes
public export
(fc:Codable Felt) => Cast Felt a => Cast a Felt => Codable a where
  size = size @{fc}
  encode v = encode @{fc} (cast v)
  decode seg = let (v,seg2) = decode @{fc} seg in (cast v, seg2)

public export
Codable Segment where
  size = Nothing
  encode s = singletonSegment (size s) ++ s
  decode seg = let (l,seg2) = (unsafeHead seg, unsafeTail seg) in (unsafeTake l seg2, unsafeDrop l seg2)

public export
(ca:Codable a) => (cb:Codable b) => Codable (a,b) where
  size = case (size @{ca}, size @{cb}) of
    (Just as, Just bs) => Just (as + bs)
    _ => Nothing
  encode (av,bv) = encode av ++ encode bv
  decode s = let (av,s2) = decode @{ca} s in
    let (bv,s3) = decode @{cb} s2 in ((av,bv),s3)

public export
(ca:Codable a) => Codable (Maybe a) where
  size = Nothing
  encode Nothing = singletonSegment 0
  encode (Just av) = singletonSegment 1 ++ encode av
  decode seg = let (l,seg2) = (unsafeHead seg, unsafeTail seg) in if l == 0
    then (Nothing, seg2)
    else let (av,seg3) = decode @{ca} seg2 in (Just av,seg3)


-- Todo: Just a sketch with out big int wont work
-- public export
-- (ca:Codable a) => Codable (List a) where
--   size = Nothing
--   encode ls = foldl (++) [singletonSegment $ cast $ length ls] (map encode ls)
--   decode seg = let (l,seg2) = (unsafeHead seg, unsafeTail seg) in decodeElem (cast l) seg2
--     -- Todo: Tail rec version would be nicer
--     where decodeElem : Int -> Segment -> (List a, Segment)
--           decodeElem 0 s = ([],s)
--           decodeElem n s = let (av,s2) = decode s in
--             let (ls,s3) = decodeElem (n-1) s2 in (av::ls,s3)

-- public export
-- (ca:Codable a) => (n:Nat) => Codable (Vect n a) where
--   size = case (size @{ca}) of
--     (Just as) => Just ((cast n) * as)
--     _ => Nothing
--     Todo: empty Segment would be nice
--   encode vs = listToSegment $ foldl (++) Nil (map (segmentToList . encode) vs)
--   decode seg = decodeElem n seg
--     -- Todo: Tail rec version would be nicer
--     where decodeElem : Nat -> Segment -> (List a, Segment)
--           decodeElem Z s = ([],s)
--           decodeElem (S n) s = let (av,s2) = decode s in
--             let (ls,s3) = decodeElem n s2 in (av::ls,s3)
