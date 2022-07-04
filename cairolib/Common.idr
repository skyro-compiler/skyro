module Common

import public Common.Felt

data World : Type where [external]

public export
data CairoRes : Type -> Type where
     MkCairoRes : (1 _ : World) -> (result : a) -> CairoRes a

public export
PrimCairo : Type -> Type
PrimCairo a = (1 _ : World) -> CairoRes a

public export
PrimCairoUnit : Type
PrimCairoUnit = (1 _ : World) -> World

public export
data Cairo : Type -> Type where
    MkCairo : (1 _ : PrimCairo a) -> Cairo a

public export %inline
fromPrimCairo : (1 _ : PrimCairo a) -> Cairo a
fromPrimCairo = MkCairo 

public export %inline
fromPrimCairoUnit : (1 _ : PrimCairoUnit) -> Cairo ()
fromPrimCairoUnit f = MkCairo (\s => MkCairoRes (f s) ())

public export %inline
toPrimCairo : (1 ca : Cairo a) -> PrimCairo a
toPrimCairo (MkCairo f) = f
 


{-
-- Specializing Functor for performance
public export -- %spec f,ca
map : (f : (a -> b)) -> (1 ca : Cairo a) -> Cairo b
map f (MkCairo ma) = MkCairo 
      (\s => let MkCairoRes s' a = ma s
              in MkCairoRes s' (f a))

-- Specializing Applicative for performance
public export -- %spec v
pure : (v:a) -> Cairo a
pure a = MkCairo (\s => MkCairoRes s a)

public export -- %spec cf,ca
(<*>) : (cf : Cairo (a -> b)) -> (ca : Cairo a) -> Cairo b
(MkCairo mf) <*> (MkCairo ma) = 
  MkCairo (\s => let MkCairoRes s' f = mf s
                     MkCairoRes s'' a = ma s'
                  in MkCairoRes s'' (f a))

-- Specializing Monad for performance
public export -- %spec ca,f
(>>=) : (1 ca: Cairo a) -> (1 f: (a -> Cairo b)) -> Cairo b
(MkCairo ma) >>= f = 
  MkCairo (\s => let MkCairoRes s' a = ma s 
                  in toPrimCairo (f a) s')
 
-- This is important for performance
public export -- %spec ma,mb
(>>) : (ma: Cairo ()) -> (mb: (Cairo a)) -> Cairo a
(MkCairo ma) >> (MkCairo mb) = 
  MkCairo (\s => let MkCairoRes s' _ = ma s in mb s')
 -}

public export %inline 
Functor Cairo where
   -- map : (f : (a -> b)) -> (1 ca : Cairo a) -> Cairo b
    map f (MkCairo ma) = MkCairo 
      (\s => let MkCairoRes s' a = ma s
              in MkCairoRes s' (f a))

public export %inline
Applicative Cairo where
    pure a = MkCairo (\s => MkCairoRes s a)
    (MkCairo mf) <*> (MkCairo ma) = 
      MkCairo (\s => let MkCairoRes s' f = mf s
                         MkCairoRes s'' a = ma s'
                      in MkCairoRes s'' (f a))

public export %inline
Monad Cairo where    
   (MkCairo ma) >>= f = 
     MkCairo (\s => let MkCairoRes s' a = ma s 
                     in toPrimCairo (f a) s')
   -- join x = x >>= id


--------------------------------------------
-- Traversable specialised for performance.
public export -- %spec f
traverse : (f: (a -> Cairo b)) -> (la: List a) -> Cairo (List b)
traverse f xs = traverse' xs []
  where 
    traverse' : List a -> List b -> Cairo (List b)
    traverse' [] acc = pure (reverse acc)
    traverse' (x :: xs) acc = traverse' xs (!(f x) :: acc)
