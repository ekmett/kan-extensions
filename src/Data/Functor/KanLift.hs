{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-------------------------------------------------------------------------------------------
-- |
-- Copyright 	: 2013 Edward Kmett and Dan Doel
-- License	: BSD
--
-- Maintainer	: Edward Kmett <ekmett@gmail.com>
-- Stability	: experimental
-- Portability	: rank N types
--
--
-------------------------------------------------------------------------------------------
module Data.Functor.KanLift
  (
  -- * Right Kan lifts
    Rift(..)
  , grift
  , universalRift
  -- * Left Kan lifts
  , Lift(..)
  , glift
  , universalLift
  ) where

import Control.Applicative
import Data.Copointed
import Data.Functor.Identity
import Data.Functor.Adjunction
import Data.Pointed

-- * Right Kan Lift

-- |
--
-- @g . 'Rift' g f => f@
--
-- This could alternately be defined directly from the universal propertly
-- in which case, we'd get 'universalRift' = 'UniversalRift', but then the usage would
-- suffer.
--
-- @
-- data 'UniversalRift' g f a = forall z. 'Functor' z =>
--      'UniversalRift' (forall x. g (z x) -> f x) (z a)
-- @
--
-- We can witness the isomorphism between Rift and UniversalRift using:
--
-- @
-- riftIso1 :: Functor g => UniversalRift g f a -> Rift g f a
-- riftIso1 (UniversalRift h z) = Rift $ \g -> h $ fmap (\k -> k <$> z) g
-- @
--
-- @
-- riftIso2 :: Rift g f a -> UniversalRift g f a
-- riftIso2 (Rift e) = UniversalRift e id
-- @
--
-- @
-- riftIso1 (riftIso2 (Rift h)) =
-- riftIso1 (UniversalRift h id) =          -- by definition
-- Rift $ \g -> h $ fmap (\k -> k <$> id) g -- by definition
-- Rift $ \g -> h $ fmap id g               -- <$> = (.) and (.id)
-- Rift $ \g -> h g                         -- by functor law
-- Rift h                                   -- eta reduction
-- @
--
-- The other direction is left as an exercise for the reader.
--
-- /NB:/ This is the same construction that gives rise to @'Control.Monad.Co.CoT'@.

newtype Rift g h a =
  Rift { runRift :: forall r. g (a -> r) -> h r }

instance Functor g => Functor (Rift g h) where
  fmap f (Rift g) = Rift (g . fmap (.f))
  {-# INLINE fmap #-}

instance (Functor g, g ~ h) => Pointed (Rift g h) where
  point a = Rift (fmap ($a))
  {-# INLINE point #-}

grift :: Adjunction f _r => f (Rift f k a) -> k a
grift = rightAdjunct (\r -> leftAdjunct (runRift r) id)
{-# INLINE grift #-}

-- | The universal property of 'Rift'
universalRift :: (Functor g, Functor z) => (forall x. g (z x) -> f x) -> z y -> Rift g f y
universalRift h z = Rift $ \g -> h $ fmap (<$> z) g
{-# INLINE universalRift #-}

-- * Left Kan Lift

-- |
-- > f => g . Lift g f
-- > (forall z. f => g . z) -> Lift g f => z -- couniversal
--
-- Here we use the universal property directly as how we extract from our definition of 'Lift'.
newtype Lift g f a =
  Lift { runLift :: forall z. Functor z => (forall x. f x -> g (z x)) -> z a }

instance Functor (Lift g h) where
  fmap f (Lift g) = Lift (fmap f . g)
  {-# INLINE fmap #-}

instance (Functor g, g ~ h) => Copointed (Lift g h) where
  copoint x = runIdentity (runLift x (fmap Identity))
  {-# INLINE copoint #-}

-- |
--
-- @f => g ('Lift' g f a)@
glift :: Adjunction l g => k a -> g (Lift g k a)
glift = leftAdjunct (\lka -> Lift (\k2gz -> rightAdjunct k2gz lka))
{-# INLINE glift #-}

-- | The universal property of 'Lift'
universalLift :: Functor z => Lift g f y -> (forall x. f x -> g (z x)) -> z y
universalLift = runLift
{-# INLINE universalLift #-}
