{-# LANGUAGE Rank2Types, GADTs #-}
{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 706
{-# LANGUAGE PolyKinds #-}
#endif
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-------------------------------------------------------------------------------------------
-- |
-- Copyright 	: 2008-2016 Edward Kmett
-- License	: BSD
--
-- Maintainer	: Edward Kmett <ekmett@gmail.com>
-- Stability	: experimental
-- Portability	: rank 2 types
--
-- * Right Kan Extensions
-------------------------------------------------------------------------------------------
module Data.Functor.Kan.Ran
  (
    Ran(..)
  , toRan, fromRan
  , gran
  , composeRan, decomposeRan
  , adjointToRan, ranToAdjoint
  , composedAdjointToRan, ranToComposedAdjoint
  , repToRan, ranToRep
  , composedRepToRan, ranToComposedRep
  ) where

import Data.Functor.Adjunction
import Data.Functor.Composition
import Data.Functor.Identity
import Data.Functor.Rep

-- | The right Kan extension of a 'Functor' h along a 'Functor' g.
--
-- We can define a right Kan extension in several ways. The definition here is obtained by reading off
-- the definition in of a right Kan extension in terms of an End, but we can derive an equivalent definition
-- from the universal property.
--
-- Given a 'Functor' @h : C -> D@ and a 'Functor' @g : C -> C'@, we want to extend @h@ /back/ along @g@
-- to give @Ran g h : C' -> D@, such that the natural transformation @'gran' :: Ran g h (g a) -> h a@ exists.
--
-- In some sense this is trying to approximate the inverse of @g@ by using one of
-- its adjoints, because if the adjoint and the inverse both exist, they match!
--
-- > Hask -h-> Hask
-- >   |       +
-- >   g      /
-- >   |    Ran g h
-- >   v    /
-- > Hask -'
--
-- The Right Kan extension is unique (up to isomorphism) by taking this as its universal property.
--
-- That is to say given any @K : C' -> D@ such that we have a natural transformation from @k.g@ to @h@
-- @(forall x. k (g x) -> h x)@ there exists a canonical natural transformation from @k@ to @Ran g h@.
-- @(forall x. k x -> Ran g h x)@.
--
-- We could literally read this off as a valid Rank-3 definition for 'Ran':
--
-- @
-- data Ran' g h a = forall z. 'Functor' z => Ran' (forall x. z (g x) -> h x) (z a)
-- @
--
-- This definition is isomorphic the simpler Rank-2 definition we use below as witnessed by the
--
-- @
-- ranIso1 :: Ran g f x -> Ran' g f x
-- ranIso1 (Ran e) = Ran' e id
-- @
--
-- @
-- ranIso2 :: Ran' g f x -> Ran g f x
-- ranIso2 (Ran' h z) = Ran $ \\k -> h (k \<$\> z)
-- @
--
-- @
-- ranIso2 (ranIso1 (Ran e)) ≡ -- by definition
-- ranIso2 (Ran' e id) ≡       -- by definition
-- Ran $ \\k -> e (k \<$\> id)    -- by definition
-- Ran $ \\k -> e (k . id)      -- f . id = f
-- Ran $ \\k -> e k             -- eta reduction
-- Ran e
-- @
--
-- The other direction is left as an exercise for the reader.
newtype Ran g h a = Ran { runRan :: forall b. (a -> g b) -> h b }

instance Functor (Ran g h) where
  fmap f m = Ran (\k -> runRan m (k . f))
  {-# INLINE fmap #-}

-- | The universal property of a right Kan extension.
toRan :: Functor k => (forall a. k (g a) -> h a) -> k b -> Ran g h b
toRan s t = Ran (s . flip fmap t)
{-# INLINE toRan #-}

-- | 'toRan' and 'fromRan' witness a higher kinded adjunction. from @(`'Compose'` g)@ to @'Ran' g@
--
-- @
-- 'toRan' . 'fromRan' ≡ 'id'
-- 'fromRan' . 'toRan' ≡ 'id'
-- @
fromRan :: (forall a. k a -> Ran g h a) -> k (g b) -> h b
fromRan s kgb = runRan (s kgb) id
{-# INLINE fromRan #-}

-- |
-- @
-- 'composeRan' . 'decomposeRan' ≡ 'id'
-- 'decomposeRan' . 'composeRan' ≡ 'id'
-- @
composeRan :: Composition compose => Ran f (Ran g h) a -> Ran (compose f g) h a
composeRan r = Ran (\f -> runRan (runRan r (decompose . f)) id)
{-# INLINE composeRan #-}

decomposeRan :: (Composition compose, Functor f) => Ran (compose f g) h a -> Ran f (Ran g h) a
decomposeRan r = Ran (\f -> Ran (\g -> runRan r (compose . fmap g . f)))
{-# INLINE decomposeRan #-}

-- |
--
-- @
-- 'adjointToRan' . 'ranToAdjoint' ≡ 'id'
-- 'ranToAdjoint' . 'adjointToRan' ≡ 'id'
-- @
adjointToRan :: Adjunction f g => f a -> Ran g Identity a
adjointToRan f = Ran (\a -> Identity $ rightAdjunct a f)
{-# INLINE adjointToRan #-}

ranToAdjoint :: Adjunction f g => Ran g Identity a -> f a
ranToAdjoint r = runIdentity (runRan r unit)
{-# INLINE ranToAdjoint #-}

-- |
--
-- @
-- 'composedAdjointToRan' . 'ranToComposedAdjoint' ≡ 'id'
-- 'ranToComposedAdjoint' . 'composedAdjointToRan' ≡ 'id'
-- @
ranToComposedAdjoint :: Adjunction f g => Ran g h a -> h (f a)
ranToComposedAdjoint r = runRan r unit
{-# INLINE ranToComposedAdjoint #-}

composedAdjointToRan :: (Adjunction f g, Functor h) => h (f a) -> Ran g h a
composedAdjointToRan f = Ran (\a -> fmap (rightAdjunct a) f)
{-# INLINE composedAdjointToRan #-}

-- | This is the natural transformation that defines a Right Kan extension.
gran :: Ran g h (g a) -> h a
gran (Ran f) = f id
{-# INLINE gran #-}

repToRan :: Representable u => Rep u -> a -> Ran u Identity a
repToRan e a = Ran $ \k -> Identity $ index (k a) e
{-# INLINE repToRan #-}

ranToRep :: Representable u => Ran u Identity a -> (Rep u, a)
ranToRep (Ran f) = runIdentity $ f (\a -> tabulate $ \e -> (e, a))
{-# INLINE ranToRep #-}

ranToComposedRep :: Representable u => Ran u h a -> h (Rep u, a)
ranToComposedRep (Ran f) = f (\a -> tabulate $ \e -> (e, a))
{-# INLINE ranToComposedRep #-}

composedRepToRan :: (Representable u, Functor h) => h (Rep u, a) -> Ran u h a
composedRepToRan hfa = Ran $ \k -> fmap (\(e, a) -> index (k a) e) hfa
{-# INLINE composedRepToRan #-}
