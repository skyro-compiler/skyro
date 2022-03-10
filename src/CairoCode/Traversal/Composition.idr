module CairoCode.Traversal.Composition

import CairoCode.CairoCode
import CairoCode.Traversal.Base
import Utils.Lens


{-
 Executes f1 and f2 on the same value, but uses state after f1 for f2 and discards value after f1
 start - value & state -----> f1 - value -> _
     | - value -> f2 <- state -|
                   | - value & state -> end
-}
export
seqTraversal : (InstVisit b -> Traversal s ()) -> (InstVisit b -> Traversal s a) -> (InstVisit b -> Traversal s a)
seqTraversal f1 f2 = (\inst => f1 inst >>= (\_ => f2 inst))


{-
 Executes f1 and f2 on the same value, but uses state after f1 for f2 and returns the tuple of the f1 & f2 values
 start - value & state -----> f1 - value -|
     | - value -> f2 <- state -|          v
                   | - value ----> build tuple
                   | - state -> end <- value |
-}
export
joinedTraversal : (InstVisit c -> Traversal s a) -> (InstVisit c -> Traversal s b) -> (InstVisit c -> Traversal s (a,b))
joinedTraversal f1 f2 = (\inst => f1 inst >>= (\av => map (\bv => (av,bv)) (f2 inst)))

{-
 Executes f1 which returns multiple values and then executing f2 on each (routing through the state) collecting the results in a monoid over  <+>
 start - value & state -----> f1 - state & [value] -> for each value : f2 - state & [value]* -> end
 *monoid integrating all f2 results (probably a list)
-}
export
chainedTraversal : Monoid a => (InstVisit b -> Traversal s (List (InstVisit c))) -> (InstVisit c -> Traversal s a) -> (InstVisit b -> Traversal s a)
chainedTraversal f1 f2 = (\inst => f1 inst >>= (\ls => foldlM (\r, inst => (f2 inst) >>= (\rn => pure $ r <+> rn)) neutral ls) )

{-
 Executes f1 which returns multiple values and then executing f2 on each throwing away the result (but routing through the state)
 start - value & state -----> f1 - state & [value] -> for each value : f2 - [value] -> _
                               | - [value] -------> end <------ state - |
-}
export
traverseTransform : (InstVisit b -> Traversal s (List (InstVisit c))) -> (InstVisit c -> Traversal s ()) -> (InstVisit b -> Traversal s (List (InstVisit c)))
traverseTransform f1 f2 = (\inst => f1 inst >>= (\ls => map (\_ => ls) (foldlM (\_, inst => f2 inst) () ls)))

{-
 Executes trav but on a sub-state identified by lens
 start - value & os -> (lens : - value & is -> trav - value & is ->) - value & os -> end
-}
export
lensTraversal : Lens os is -> (InstVisit a -> Traversal is r) -> (InstVisit a -> Traversal os r)
lensTraversal lens trav = (composeState lens) . trav


{-
 Executes trav but on a tupled state using the left part
 start - value & (ls,rs) -> (left : -> value & ls -> trav -> value & ls) - value & (ls,rs) -> end
-}
export
leftTraversal : (InstVisit a -> Traversal ls r) -> (InstVisit a -> Traversal (ls, rs) r)
leftTraversal trav = lensTraversal leftLens trav

{-
 Executes trav but on a tupled state using the right part
 start - value & (ls,rs) -> (left : -> value & rs -> trav -> value & rs) - value & (ls,rs) -> end
-}
export
rightTraversal : (InstVisit a -> Traversal rs r) -> (InstVisit a -> Traversal (ls, rs) r)
rightTraversal trav = lensTraversal rightLens trav


{-
 Executes fn and if defined (Just) uses the result otherwise (Nothing) uses fallback to define the value
 start - value & state -> fn | case Just: - value & state --------------------------v
     |                       | case Nothing: - state -> fallback - value & state -> end
     | - value -----------------------------------------^
-}
export
fallbackTraversal : (InstVisit b ->  Traversal s (Maybe a)) -> (InstVisit b -> Traversal s a)-> (InstVisit b ->  Traversal s a)
fallbackTraversal fn fallback = (\inst => fn inst >>= (execFallback inst))
    where execFallback: InstVisit b -> Maybe a -> Traversal s a
          execFallback inst (Just av) = pure av
          execFallback inst Nothing = fallback inst
