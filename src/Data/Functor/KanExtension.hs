{-# LANGUAGE Rank2Types, GADTs #-}
{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-------------------------------------------------------------------------------------------
-- |
-- Module	: Data.Functor.KanExtension
-- Copyright 	: 2008-2011 Edward Kmett
-- License	: BSD
--
-- Maintainer	: Edward Kmett <ekmett@gmail.com>
-- Stability	: experimental
-- Portability	: rank 2 types
--
-------------------------------------------------------------------------------------------
module Data.Functor.KanExtension
  (
  -- * Right Kan Extensions
    Ran(..)
  , toRan, fromRan
  , gran
  , composeRan, decomposeRan
  , adjointToRan, ranToAdjoint
  , composedAdjointToRan, ranToComposedAdjoint
  -- * Left Kan Extensions
  , Lan(..)
  , toLan, fromLan
  , glan
  , composeLan, decomposeLan
  , adjointToLan, lanToAdjoint
  , composedAdjointToLan, lanToComposedAdjoint
  ) where

import Data.Functor.Identity
import Data.Functor.Adjunction
import Data.Functor.Composition
import Data.Functor.Apply
import Control.Applicative

-- | The right Kan extension of a 'Functor' h along a 'Functor' g.
--
-- We can define a right Kan extension in several ways. The definition here is obtained by reading off
-- the definition in of a right Kan extension in terms of an End, but we can derive an equivalent definition
-- from the universal property.
--
-- Given a 'Functor' @h : C -> D@ and a 'Functor' @g : C -> C'@, we want to find extend @h@ /back/ along @g@
-- to give @Ran g h : C' -> C@, such that the natural transformation @'gran' :: Ran g h (g a) -> h a@ exists.
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
-- That is to say given any @K : C' -> C@ such that we have a natural transformation from @k.g@ to @h@
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
--
-- ranIso2 :: Ran' g f x -> Ran g f x
-- ranIso2 (Ran' h z) = Ran $ \k -> h (k <$> z)
-- @
--
-- @
-- ranIso2 (ranIso1 (Ran e)) ≡ -- by definition
-- ranIso2 (Ran' e id) ≡       -- by definition
-- Ran $ \k -> e (k <$> id)    -- by definition
-- Ran $ \k -> e (k . id)      -- f . id = f
-- Ran $ \k -> e k             -- eta reduction
-- Ran e
-- @
--
-- The other direction is left as an exercise for the reader.
newtype Ran g h a = Ran { runRan :: forall b. (a -> g b) -> h b }

instance Functor (Ran g h) where
  fmap f m = Ran (\k -> runRan m (k . f))

-- | The universal property of a right Kan extension.
toRan :: Functor k => (forall a. k (g a) -> h a) -> k b -> Ran g h b
toRan s t = Ran (s . flip fmap t)

-- | 'toRan' and 'fromRan' witness a higher kinded adjunction. from @(`'Compose'` g)@ to @'Ran' g@
--
-- @
-- 'toRan' . 'fromRan' ≡ 'id'
-- 'fromRan' . 'toRan' ≡ 'id'
-- @
fromRan :: (forall a. k a -> Ran g h a) -> k (g b) -> h b
fromRan s = flip runRan id . s

-- |
-- @
-- 'composeRan' . 'decomposeRan' ≡ 'id'
-- 'decomposeRan' . 'composeRan' ≡ 'id'
-- @
composeRan :: Composition compose => Ran f (Ran g h) a -> Ran (compose f g) h a
composeRan r = Ran (\f -> runRan (runRan r (decompose . f)) id)

decomposeRan :: (Composition compose, Functor f) => Ran (compose f g) h a -> Ran f (Ran g h) a
decomposeRan r = Ran (\f -> Ran (\g -> runRan r (compose . fmap g . f)))

-- |
--
-- @
-- 'adjointToRan' . 'ranToAdjoint' ≡ 'id'
-- 'ranToAdjoint' . 'adjointToRan' ≡ 'id'
-- @
adjointToRan :: Adjunction f g => f a -> Ran g Identity a
adjointToRan f = Ran (\a -> Identity $ rightAdjunct a f)

ranToAdjoint :: Adjunction f g => Ran g Identity a -> f a
ranToAdjoint r = runIdentity (runRan r unit)

-- |
--
-- @
-- 'composedAdjointToRan' . 'ranToComposedAdjoint' ≡ 'id'
-- 'ranToComposedAdjoint' . 'composedAdjointToRan' ≡ 'id'
-- @
ranToComposedAdjoint :: Adjunction f g => Ran g h a -> h (f a)
ranToComposedAdjoint r = runRan r unit

composedAdjointToRan :: (Adjunction f g, Functor h) => h (f a) -> Ran g h a
composedAdjointToRan f = Ran (\a -> fmap (rightAdjunct a) f)

-- | This is the natural transformation that defines a Right Kan extension.
gran :: Ran g h (g a) -> h a
gran (Ran f) = f id

-- | The left Kan extension of a 'Functor' @h@ along a 'Functor' @g@.
data Lan g h a where
  Lan :: (g b -> a) -> h b -> Lan g h a

instance Functor (Lan f g) where
  fmap f (Lan g h) = Lan (f . g) h

instance (Functor g, Apply h) => Apply (Lan g h) where
  Lan kxf x <.> Lan kya y =
    Lan (\k -> kxf (fmap fst k) (kya (fmap snd k))) ((,) <$> x <.> y)

instance (Functor g, Applicative h) => Applicative (Lan g h) where
  pure a = Lan (const a) (pure ())
  Lan kxf x <*> Lan kya y =
    Lan (\k -> kxf (fmap fst k) (kya (fmap snd k))) (liftA2 (,) x y)

-- | The universal property of a left Kan extension.
toLan :: Functor f => (forall a. h a -> f (g a)) -> Lan g h b -> f b
toLan s (Lan f v) = fmap f (s v)

-- | 'fromLan' and 'toLan' witness a (higher kinded) adjunction between @'Lan' g@ and @(`Compose` g)@
--
-- @
-- 'toLan' . 'fromLan' ≡ 'id'
-- 'fromLan' . 'toLan' ≡ 'id'
-- @
fromLan :: (forall a. Lan g h a -> f a) -> h b -> f (g b)
fromLan s = s . glan

-- |
--
-- @
-- 'adjointToLan' . 'lanToAdjoint' ≡ 'id'
-- 'lanToAdjoint' . 'adjointToLan' ≡ 'id'
-- @
adjointToLan :: Adjunction f g => g a -> Lan f Identity a
adjointToLan = Lan counit . Identity

lanToAdjoint :: Adjunction f g => Lan f Identity a -> g a
lanToAdjoint (Lan f v) = leftAdjunct f (runIdentity v)

-- | 'lanToComposedAdjoint' and 'composedAdjointToLan' witness the natural isomorphism between @Lan f h@ and @Compose h g@ given @f -| g@
--
-- @
-- 'composedAdjointToLan' . 'lanToComposedAdjoint' ≡ 'id'
-- 'lanToComposedAdjoint' . 'composedAdjointToLan' ≡ 'id'
-- @
lanToComposedAdjoint :: (Functor h, Adjunction f g) => Lan f h a -> h (g a)
lanToComposedAdjoint (Lan f v) = fmap (leftAdjunct f) v

composedAdjointToLan :: Adjunction f g => h (g a) -> Lan f h a
composedAdjointToLan = Lan counit

-- | 'composeLan' and 'decomposeLan' witness the natural isomorphism from @Lan f (Lan g h)@ and @Lan (f `o` g) h@
--
-- @
-- 'composeLan' . 'decomposeLan' ≡ 'id'
-- 'decomposeLan' . 'composeLan' ≡ 'id'
-- @
composeLan :: (Composition compose, Functor f) => Lan f (Lan g h) a -> Lan (compose f g) h a
composeLan (Lan f (Lan g h)) = Lan (f . fmap g . decompose) h

decomposeLan :: Composition compose => Lan (compose f g) h a -> Lan f (Lan g h) a
decomposeLan (Lan f h) = Lan (f . compose) (Lan id h)

-- | This is the natural transformation that defines a Left Kan extension.
glan :: h a -> Lan g h (g a)
glan = Lan id
