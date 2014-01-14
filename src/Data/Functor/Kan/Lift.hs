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
-- Left Kan lifts for functors over Hask, wherever they exist.
--
-- <http://ncatlab.org/nlab/show/Kan+lift>
-------------------------------------------------------------------------------------------
module Data.Functor.Kan.Lift
  (
  -- * Left Kan lifts
    Lift(..)
  , toLift, fromLift, glift
  , composeLift, decomposeLift
  , adjointToLift, liftToAdjoint
  , liftToComposedAdjoint, composedAdjointToLift
  , repToLift, liftToRep
  , liftToComposedRep, composedRepToLift
  ) where

import Data.Copointed
import Data.Functor.Adjunction
import Data.Functor.Composition
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Rep

-- * Left Kan Lift

-- |
-- > f => g . Lift g f
-- > (forall z. f => g . z) -> Lift g f => z -- couniversal
--
-- Here we use the universal property directly as how we extract from our definition of 'Lift'.
newtype Lift g f a = Lift { runLift :: forall z. Functor z => (forall x. f x -> g (z x)) -> z a }

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
toLift :: Functor z => (forall a. f a -> g (z a)) -> Lift g f b -> z b
toLift = flip runLift
{-# INLINE toLift #-}

-- | When the adjunction exists
--
-- @
-- 'fromLift' . 'toLift' ≡ 'id'
-- 'toLift' . 'fromLift' ≡ 'id'
-- @
fromLift :: Adjunction l u => (forall a. Lift u f a -> z a) -> f b -> u (z b)
fromLift f = fmap f . glift
{-# INLINE fromLift #-}

-- |
--
-- @
-- 'composeLift' . 'decomposeLift' = 'id'
-- 'decomposeLift' . 'composeLift' = 'id'
-- @
composeLift :: (Composition compose, Functor f, Functor g) => Lift f (Lift g h) a -> Lift (compose g f) h a
composeLift (Lift m) = Lift $ \h -> m $ decompose . toLift (fmap Compose . decompose . h)
{-# INLINE composeLift #-}

decomposeLift :: (Composition compose, Adjunction l g) => Lift (compose g f) h a -> Lift f (Lift g h) a
decomposeLift (Lift m) = Lift $ \h -> m (compose . fmap h . glift)
{-# INLINE decomposeLift #-}

-- | @Lift u Identity a@ is isomorphic to the left adjoint to @u@ if one exists.
--
-- @
-- 'adjointToLift' . 'liftToAdjoint' ≡ 'id'
-- 'liftToAdjoint' . 'adjointToLift' ≡ 'id'
-- @
adjointToLift :: Adjunction f u => f a -> Lift u Identity a
adjointToLift fa = Lift $ \k -> rightAdjunct (k . Identity) fa
{-# INLINE adjointToLift #-}


-- | @Lift u Identity a@ is isomorphic to the left adjoint to @u@ if one exists.
liftToAdjoint :: Adjunction f u => Lift u Identity a -> f a
liftToAdjoint = toLift (unit . runIdentity)
{-# INLINE liftToAdjoint #-}

-- |
--
-- @
-- 'repToLift' . 'liftToRep' ≡ 'id'
-- 'liftToRep' . 'repToLift' ≡ 'id'
-- @
repToLift :: Representable u => Rep u -> a -> Lift u Identity a
repToLift e a = Lift $ \k -> index (k (Identity a)) e
{-# INLINE repToLift #-}

liftToRep :: Representable u => Lift u Identity a -> (Rep u, a)
liftToRep (Lift m) = m $ \(Identity a) -> tabulate $ \e -> (e, a)
{-# INLINE liftToRep #-}

-- | @Lift u h a@ is isomorphic to the post-composition of the left adjoint of @u@ onto @h@ if such a left adjoint exists.
--
-- @
-- 'liftToComposedAdjoint' . 'composedAdjointToLift' ≡ 'id'
-- 'composedAdjointToLift' . 'liftToComposedAdjoint' ≡ 'id'
-- @
liftToComposedAdjoint :: (Adjunction f u, Functor h) => Lift u h a -> f (h a)
liftToComposedAdjoint (Lift m) = decompose $ m (leftAdjunct Compose)
{-# INLINE liftToComposedAdjoint #-}

-- | @Lift u h a@ is isomorphic to the post-composition of the left adjoint of @u@ onto @h@ if such a left adjoint exists.
composedAdjointToLift :: Adjunction f u => f (h a) -> Lift u h a
composedAdjointToLift = rightAdjunct glift
{-# INLINE composedAdjointToLift #-}

-- |
--
-- @
-- 'liftToComposedRep' . 'composedRepToLift' ≡ 'id'
-- 'composedRepToLift' . 'liftToComposedRep' ≡ 'id'
-- @
liftToComposedRep :: (Functor h, Representable u) => Lift u h a -> (Rep u, h a)
liftToComposedRep (Lift m) = decompose $ m $ \h -> tabulate $ \e -> Compose (e, h)
{-# INLINE liftToComposedRep #-}

composedRepToLift :: Representable u => Rep u -> h a -> Lift u h a
composedRepToLift e ha = Lift $ \h2uz -> index (h2uz ha) e
{-# INLINE composedRepToLift #-}
