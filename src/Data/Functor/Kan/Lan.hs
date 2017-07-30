{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
#if __GLASGOW_HASKELL__ >= 706
{-# LANGUAGE PolyKinds #-}
#endif
#if __GLASGOW_HASKELL__ >= 702 && __GLASGOW_HASKELL__ < 710
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
-- Left Kan Extensions
-------------------------------------------------------------------------------------------
module Data.Functor.Kan.Lan
  (
  -- * Left Kan Extensions
    Lan(..)
  , toLan, fromLan
  , glan
  , composeLan, decomposeLan
  , adjointToLan, lanToAdjoint
  , composedAdjointToLan, lanToComposedAdjoint
  ) where

import Control.Applicative
import Data.Functor.Adjunction
import Data.Functor.Apply
import Data.Functor.Composition
import Data.Functor.Identity

-- | The left Kan extension of a 'Functor' @h@ along a 'Functor' @g@.
data Lan g h a where
  Lan :: (g b -> a) -> h b -> Lan g h a

instance Functor (Lan f g) where
  fmap f (Lan g h) = Lan (f . g) h
  {-# INLINE fmap #-}

instance (Functor g, Apply h) => Apply (Lan g h) where
  Lan kxf x <.> Lan kya y =
    Lan (\k -> kxf (fmap fst k) (kya (fmap snd k))) ((,) <$> x <.> y)
  {-# INLINE (<.>) #-}

instance (Functor g, Applicative h) => Applicative (Lan g h) where
  pure a = Lan (const a) (pure ())
  {-# INLINE pure #-}
  Lan kxf x <*> Lan kya y =
    Lan (\k -> kxf (fmap fst k) (kya (fmap snd k))) (liftA2 (,) x y)
  {-# INLINE (<*>) #-}

-- | The universal property of a left Kan extension.
toLan :: Functor f => (forall a. h a -> f (g a)) -> Lan g h b -> f b
toLan s (Lan f v) = fmap f (s v)
{-# INLINE toLan #-}

-- | 'fromLan' and 'toLan' witness a (higher kinded) adjunction between @'Lan' g@ and @(`Compose` g)@
--
-- @
-- 'toLan' . 'fromLan' ≡ 'id'
-- 'fromLan' . 'toLan' ≡ 'id'
-- @
fromLan :: (forall a. Lan g h a -> f a) -> h b -> f (g b)
fromLan s = s . glan
{-# INLINE fromLan #-}

-- |
--
-- @
-- 'adjointToLan' . 'lanToAdjoint' ≡ 'id'
-- 'lanToAdjoint' . 'adjointToLan' ≡ 'id'
-- @
adjointToLan :: Adjunction f g => g a -> Lan f Identity a
adjointToLan = Lan counit . Identity
{-# INLINE adjointToLan #-}

lanToAdjoint :: Adjunction f g => Lan f Identity a -> g a
lanToAdjoint (Lan f v) = leftAdjunct f (runIdentity v)
{-# INLINE lanToAdjoint #-}

-- | 'lanToComposedAdjoint' and 'composedAdjointToLan' witness the natural isomorphism between @Lan f h@ and @Compose h g@ given @f -| g@
--
-- @
-- 'composedAdjointToLan' . 'lanToComposedAdjoint' ≡ 'id'
-- 'lanToComposedAdjoint' . 'composedAdjointToLan' ≡ 'id'
-- @
lanToComposedAdjoint :: (Functor h, Adjunction f g) => Lan f h a -> h (g a)
lanToComposedAdjoint (Lan f v) = fmap (leftAdjunct f) v
{-# INLINE lanToComposedAdjoint #-}

composedAdjointToLan :: Adjunction f g => h (g a) -> Lan f h a
composedAdjointToLan = Lan counit
{-# INLINE composedAdjointToLan #-}

-- | 'composeLan' and 'decomposeLan' witness the natural isomorphism from @Lan f (Lan g h)@ and @Lan (f `o` g) h@
--
-- @
-- 'composeLan' . 'decomposeLan' ≡ 'id'
-- 'decomposeLan' . 'composeLan' ≡ 'id'
-- @
composeLan :: (Composition compose, Functor f) => Lan f (Lan g h) a -> Lan (compose f g) h a
composeLan (Lan f (Lan g h)) = Lan (f . fmap g . decompose) h
{-# INLINE composeLan #-}

decomposeLan :: Composition compose => Lan (compose f g) h a -> Lan f (Lan g h) a
decomposeLan (Lan f h) = Lan (f . compose) (Lan id h)
{-# INLINE decomposeLan #-}

-- | This is the natural transformation that defines a Left Kan extension.
glan :: h a -> Lan g h (g a)
glan = Lan id
{-# INLINE glan #-}
