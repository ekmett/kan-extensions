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
-- Right and Left Kan lifts for functors over Hask.
--
-- <http://ncatlab.org/nlab/show/Kan+lift>
-------------------------------------------------------------------------------------------
module Data.Functor.KanLift
  (
  -- * Right Kan lifts
    Rift(..)
  , toRift, fromRift, grift
  , composeRift, decomposeRift
  , adjointToRift, riftToAdjoint
  , composedAdjointToRift, riftToComposedAdjoint
  , rap
  -- * Left Kan lifts
  , Lift(..)
  , toLift, fromLift, glift
  , composeLift, decomposeLift
  , adjointToLift, liftToAdjoint
  , liftToComposedAdjoint, composedAdjointToLift
  ) where

import Control.Applicative
import Data.Copointed
import Data.Functor.Adjunction
import Data.Functor.Composition
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Pointed

-- * Right Kan Lift

-- |
--
-- @g . 'Rift' g f => f@
--
-- This could alternately be defined directly from the (co)universal propertly
-- in which case, we'd get 'toRift' = 'UniversalRift', but then the usage would
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
-- There are several monads that we can form from @Rift@.
--
-- When @g@ is corepresentable (e.g. is a right adjoint) then there exists @x@ such that @g ~ (->) x@, then it follows that
--
-- @
-- Rift g g a ~
-- forall r. (x -> a -> r) -> x -> r ~
-- forall r. (a -> x -> r) -> x -> r ~
-- forall r. (a -> g r) -> g r ~
-- Codensity g r
-- @
--
-- When @f@ is a left adjoint, so that @f -| g@ then
--
-- @
-- Rift f f a ~
-- forall r. f (a -> r) -> f r ~
-- forall r. (a -> r) -> g (f r) ~
-- forall r. (a -> r) -> Adjoint f g r ~
-- Yoneda (Adjoint f g r)
-- @
--
-- An alternative way to view that is to note that whenever @f@ is a left adjoint then @f -| 'Rift' f 'Identity'@, and since @'Rift' f f@ is isomorphic to @'Rift' f 'Identity' (f a)@, this is the 'Monad' formed by the adjunction.
--
-- @'Rift' w f ~ 'Control.Monad.Co.CoT' w f@ can be a 'Monad' for any 'Comonad' @w@.
--
-- @'Rift' 'Identity' m@ can be a 'Monad' for any 'Monad' @m@, as it is isomorphic to @'Yoneda' m@.

newtype Rift g h a =
  Rift { runRift :: forall r. g (a -> r) -> h r }

instance Functor g => Functor (Rift g h) where
  fmap f (Rift g) = Rift (g . fmap (.f))
  {-# INLINE fmap #-}

instance (Functor g, g ~ h) => Pointed (Rift g h) where
  point a = Rift (fmap ($a))
  {-# INLINE point #-}

instance (Functor g, g ~ h) => Applicative (Rift g h) where
  pure a = Rift (fmap ($a))
  {-# INLINE pure #-}
  Rift mf <*> Rift ma = Rift (ma . mf . fmap (.))
  {-# INLINE (<*>) #-}

-- | Indexed applicative composition of right Kan lifts.
rap :: Functor f => Rift f g (a -> b) -> Rift g h a -> Rift f h b
rap (Rift mf) (Rift ma) = Rift (ma . mf . fmap (.))
{-# INLINE rap #-}

grift :: Adjunction f u => f (Rift f k a) -> k a
grift = rightAdjunct (\r -> leftAdjunct (runRift r) id)
{-# INLINE grift #-}

-- | The universal property of 'Rift'
toRift :: (Functor g, Functor k) => (forall x. g (k x) -> h x) -> k a -> Rift g h a
toRift h z = Rift $ \g -> h $ fmap (<$> z) g
{-# INLINE toRift #-}

-- |
-- When @f -| u@, then @f -| Rift f Identity@ and
--
-- @
-- 'toRift' . 'fromRift' ≡ 'id'
-- 'fromRift' . 'toRift' ≡ 'id'
-- @
fromRift :: Adjunction f u => (forall a. k a -> Rift f h a) -> f (k b) -> h b
fromRift f = grift . fmap f
{-# INLINE fromRift #-}

-- | @Rift f Identity a@ is isomorphic to the right adjoint to @f@ if one exists.
--
-- @
-- 'adjointToRift' . 'riftToAdjoint' ≡ 'id'
-- 'riftToAdjoint' . 'adjointToRift' ≡ 'id'
-- @
adjointToRift :: Adjunction f u => u a -> Rift f Identity a
adjointToRift ua = Rift (Identity . rightAdjunct (<$> ua))
{-# INLINE adjointToRift #-}

-- | @Rift f Identity a@ is isomorphic to the right adjoint to @f@ if one exists.
riftToAdjoint :: Adjunction f u => Rift f Identity a -> u a
riftToAdjoint (Rift m) = leftAdjunct (runIdentity . m) id
{-# INLINE riftToAdjoint #-}

-- |
--
-- @
-- 'composeRift' . 'decomposeRift' ≡ 'id'
-- 'decomposeRift' . 'composeRift' ≡ 'id'
-- @
composeRift :: (Composition compose, Adjunction g u) => Rift f (Rift g h) a -> Rift (compose g f) h a
composeRift (Rift f) = Rift (grift . fmap f . decompose)
{-# INLINE composeRift #-}

decomposeRift :: (Composition compose, Functor f, Functor g) => Rift (compose g f) h a -> Rift f (Rift g h) a
decomposeRift (Rift f) = Rift $ \far -> Rift (f . compose . fmap (\rs -> fmap (rs.) far))
{-# INLINE decomposeRift #-}


-- |
-- | @Rift f h a@ is isomorphic to the post-composition of the right adjoint of @f@ onto @h@ if such a right adjoint exists.
--
-- @
-- 'riftToComposedAdjoint' . 'composedAdjointToRift' ≡ 'id'
-- 'composedAdjointToRift' . 'riftToComposedAdjoint' ≡ 'id'
-- @

riftToComposedAdjoint :: Adjunction f u => Rift f h a -> u (h a)
riftToComposedAdjoint (Rift m) = leftAdjunct m id
{-# INLINE riftToComposedAdjoint #-}

composedAdjointToRift :: (Functor h, Adjunction f u) => u (h a) -> Rift f h a
composedAdjointToRift uha = Rift $ rightAdjunct (\b -> fmap b <$> uha)
{-# INLINE composedAdjointToRift #-}

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

-- toLift decompose :: Compose f => Lift g (compose g f) a -> f a

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
