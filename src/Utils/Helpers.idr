module Utils.Helpers

import Data.SortedSet
import Data.SortedMap
import Data.List

%hide Prelude.toList

export
setMap : Ord b => (a -> b) -> SortedSet a -> SortedSet b
setMap fn setv = fromList $ map fn (toList setv)

export
mapMap : Ord k2 => ((k1,a) -> (k2, b)) -> SortedMap k1 a -> SortedMap k2 b
mapMap fn mapv = fromList $ map fn (toList mapv)

export
maybeMap : (a -> b) -> Maybe a -> Maybe b
maybeMap _ Nothing = Nothing
maybeMap f (Just av) = Just (f av)

export
mapValueMap : Ord k => (a -> b) -> SortedMap k a -> SortedMap k b
mapValueMap fn mapv = mapMap (\(k,v) => (k, fn v)) mapv

export
mapFilter : Ord k => ((k,a) -> Bool) -> SortedMap k a -> SortedMap k a
mapFilter fn mapv = fromList $ filter fn (toList mapv)

export
setFilter : Ord k => (k -> Bool) -> SortedSet k -> SortedSet k
setFilter fn setv = fromList $ filter fn (toList setv)

export
keyFilter : Ord k => (k -> Bool) -> SortedMap k a -> SortedMap k a
keyFilter fn mapv = mapFilter (fn . fst) mapv

export
valueFilter : Ord k => (a -> Bool) -> SortedMap k a -> SortedMap k a
valueFilter fn mapv = mapFilter (fn . snd) mapv


export
[dropDuplicateKeysSemigroup] Semigroup (SortedMap k v) where
  (<+>) = mergeLeft

export
[dropDuplicateKeysMonoid] (Ord k) => Monoid (SortedMap k v) using dropDuplicateKeysSemigroup where
  neutral = empty

export
separate : (sep:String) -> (ss:List String) -> String
separate _ [] = ""
separate _ [s] = s
separate sep (s::ss) = s ++ sep ++ separate sep ss
