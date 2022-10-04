-- Finger trees are known for their static overhead despite having an efficient time complexity
-- But without the problematic parts

import Cairo
import Data.Maybe
import Data.List

data Digit a
    = One a
    | Two a a
    | Three a a a
    | Four a a a a

Foldable Digit where
    foldr f z (One a) = f a z
    foldr f z (Two a b) = f a (f b z)
    foldr f z (Three a b c) = f a (f b (f c z))
    foldr f z (Four a b c d) = f a (f b (f c (f d z)))

    foldl f z (One a) = f z a
    foldl f z (Two b a) = f (f z b) a
    foldl f z (Three c b a) = f (f (f z c) b) a
    foldl f z (Four d c b a) = f (f (f (f z d) c) b) a

data Node a
  = Node2 a a
  | Node3 a a a

data FingerTree a
  = Empty
  | Single a
  | Deep (Digit a) (FingerTree (Node a)) (Digit a)

prepend : a -> FingerTree a -> FingerTree a
prepend e Empty = Single e
prepend e (Single a) = Deep (One e) Empty (One a)
prepend e (Deep (One a) m sf) = Deep (Two e a) m sf
prepend e (Deep (Two a b) m sf) = Deep (Three e a b) m sf
prepend e (Deep (Three a b c) m sf) = Deep (Four e a b c) m sf
prepend e (Deep (Four a b c d) m sf) = Deep (Two e a) (prepend (Node3 b c d) m) sf

append : FingerTree a -> a -> FingerTree a
append Empty e = Single e
append (Single a) e = Deep (One a) Empty (One e)
append (Deep pr m (One a)) e = Deep pr m (Two a e)
append (Deep pr m (Two a b)) e = Deep pr m (Three a b e)
append (Deep pr m (Three a b c)) e = Deep pr m (Four a b c e)
append (Deep pr m (Four a b c d)) e = Deep pr (append m (Node3 a b c)) (Two d e)

concat3 : FingerTree a -> List a -> FingerTree a -> FingerTree a
concat3 Empty xs rt = foldr prepend rt xs
concat3 lt xs Empty = foldl append lt xs
concat3 (Single a) xs rt = prepend a (foldr (prepend) rt xs)
concat3 lt xs (Single a) = append (foldl (append) lt xs) a
concat3 (Deep pr1 m1 sf1) xs (Deep pr2 m2 sf2) = Deep pr1 (concat3 m1 (nodes ((toList sf1) ++ xs ++ (toList pr2))) m2) sf2
    where nodes : List a -> List (Node a)
          nodes [a, b] = [Node2 a b]
          nodes [a, b, c] = [Node3 a b c]
          nodes [a, b, c, d] = [Node2 a b, Node2 c d]
          nodes (a :: b :: c :: xs) = (Node3 a b c) :: (nodes xs)
          nodes _ = assert_total $ idris_crash "should not happen as concatenation of 3 lists where to should be nonempty should always have at least 2 elems"

concatenate :  FingerTree a -> FingerTree a -> FingerTree a
concatenate lt rt = concat3 lt [] rt

toTree : Foldable fl => fl a -> FingerTree a
toTree elems = foldl append Empty elems

data ViewL : (Type -> Type) -> Type -> Type where
    NilL : ViewL s a
    ConsL : a -> s a -> ViewL s a

viewL : FingerTree a -> ViewL FingerTree a
viewL Empty = NilL
viewL (Single x) = ConsL x Empty
viewL (Deep (One x) m sf) = ConsL x (deepL (viewL m))
    where deepL : ViewL FingerTree (Node a) -> FingerTree a
          deepL NilL = toTree sf
          deepL (ConsL (Node2 a b) m') = Deep (Two a b) m' sf
          deepL (ConsL (Node3 a b c) m') = Deep (Three a b c) m' sf
viewL (Deep (Two a b) m sf) = ConsL a (Deep (One b) m sf )
viewL (Deep (Three a b c) m sf) = ConsL a (Deep (Two b c) m sf )
viewL (Deep (Four a b c d) m sf) = ConsL a (Deep (Three b c d) m sf )

isEmpty : FingerTree a -> Bool
isEmpty x = case viewL x of
    NilL => True
    (ConsL _ _) => False

headL : FingerTree a -> Maybe a
headL x = case viewL x of
    NilL => Nothing
    (ConsL e _) => Just e

tailL : FingerTree a -> Maybe (FingerTree a)
tailL x = case viewL x of
    NilL => Nothing
    (ConsL _ xs) => Just xs

data ViewR : (Type -> Type) -> Type -> Type where
    NilR : ViewR s a
    ConsR : s a -> a -> ViewR s a

viewR : FingerTree a -> ViewR FingerTree a
viewR Empty = NilR
viewR (Single x) = ConsR Empty x
viewR (Deep pr m (One x)) = ConsR (deepR (viewR m)) x
    where deepR : ViewR FingerTree (Node a) -> FingerTree a
          deepR NilR = toTree pr
          deepR (ConsR m' (Node2 a b)) = Deep pr m' (Two a b)
          deepR (ConsR m' (Node3 a b c) ) = Deep pr m' (Three a b c)
viewR (Deep pr m (Two a b)) = ConsR (Deep pr m (One a)) b
viewR (Deep pr m (Three a b c)) = ConsR (Deep pr m (Two a b)) c
viewR (Deep pr m (Four a b c d)) = ConsR (Deep pr m (Three a b c)) d

headR : FingerTree a -> Maybe a
headR x = case viewR x of
    NilR => Nothing
    (ConsR _ e) => Just e

tailR : FingerTree a -> Maybe (FingerTree a)
tailR x = case viewR x of
    NilR => Nothing
    (ConsR xs _) => Just xs

Foldable FingerTree where
    foldr fn state fa = case viewR fa of
        NilR => state
        (ConsR xs x) => foldr fn (fn x state) xs

    foldl fn state fa = case viewL fa of
        NilL => state
        (ConsL x xs) => foldl fn (fn state x) xs

main : Cairo ()
main = do
    _ <- traverse output (toList (append (prepend 1 (concatenate (toTree [2,3]) (toTree [4,5]))) 6))
    pure ()
