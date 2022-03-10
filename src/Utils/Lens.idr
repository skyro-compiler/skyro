module Utils.Lens

-- Note: Their are lenses out their for Idris
--          https://github.com/HuwCampbell/idris-lens/blob/master/Control/Lens/Types.idr
--          https://github.com/idris-hackers/idris-lens/blob/master/Lens.idr
-- However, they are over complicated for performance and composability reasons.
--  Conclusion: Use a custom bare minimum (easy understandable) now and if needed replace with a more sophisticated implementation later (if needed)

public export
record Lens w p where
    constructor MkLens
    get : w -> p
    update : w -> (p -> p) -> w     -- Defining over update (instead of set) seems more efficient (without getting to complex)

-- Implicit versions of the accessors
export
(.set) : Lens w p -> w -> p -> w
(.set)  lens wv pv = lens.update wv (\_ => pv)

export
set : Lens w p -> w -> p -> w
set lens wv pv = lens.set wv pv

-- Views: Not yet needed remove if it stays that way
public export
record View w p where
    constructor MkView
    lens : Lens w p
    value : w

getV : View w p -> p
getV (MkView lens wv) = lens.get wv

setV : View w p -> p -> View w p
setV (MkView lens wv) pv = MkView lens (lens.set wv pv)

updateV : View w p -> (p -> p) -> View w p
updateV (MkView lens wv) fn = MkView lens (lens.update wv fn)

Semigroup p => Semigroup (View w p) where
    (<+>) vl vr = updateV vl (<+> (getV vr))

-- Compositors
export
join : Lens w m -> Lens m p -> Lens w p
join lo li = MkLens (\wv => li.get $ lo.get wv) (\wv,fn => lo.update wv (\mv => li.update mv fn))

-- identity
export
idLens : Lens a a
idLens = MkLens id (\av,fn => fn av)

-- Tuple
export
leftLens : Lens (a,b) a
leftLens = MkLens (\(av,bv) => av) (\(av,bv),fn => (fn av,bv))

export
rightLens : Lens (a,b) b
rightLens = MkLens (\(av,bv) => bv) (\(av,bv),fn => (av,fn bv))

-- List
-- Not the nicest but I do not implement Prisms just for this - especially if the normal use is to fail anyway
export
headFailLens : Lens (List a) a
headFailLens = MkLens read update
    where read : List a -> a
          read (head::xs) = head
          read _ = assert_total $ idris_crash "List was empty"
          update : List a -> (a -> a) -> List a
          update (head::xs) headUpdate = (headUpdate head)::xs
          update _ _ = assert_total $ idris_crash "List was empty"

export
tailFailLens : Lens (List a) (List a)
tailFailLens = MkLens read update
    where read : List a -> List a
          read (head::xs) = xs
          read _ = assert_total $ idris_crash "List was empty"
          update : List a -> (List a ->  List a) -> List a
          update (head::xs) tailUpdate = head::(tailUpdate xs)
          update _ _ = assert_total $ idris_crash "List was empty"
