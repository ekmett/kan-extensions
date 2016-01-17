{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

#if __GLASGOW_HASKELL__ >= 702 && __GLASGOW_HASKELL__ < 710
{-# LANGUAGE Trustworthy #-}
#endif
-------------------------------------------------------------------------------------------
-- |
-- Copyright 	: 2013-2016 Edward Kmett and Dan Doel
-- License	: BSD
--
-- Maintainer	: Edward Kmett <ekmett@gmail.com>
-- Stability	: experimental
-- Portability	: rank N types
--
-- @'Day' f -| 'Curried' f@
--
-- @'Day' f ~ 'Compose' f@ when f preserves colimits / is a left adjoint. (Due in part to the
-- strength of all functors in Hask.)
--
-- So by the uniqueness of adjoints, when f is a left adjoint, @'Curried' f ~ 'Rift' f@
-------------------------------------------------------------------------------------------
module Data.Functor.Day.Curried
  (
  -- * Right Kan lifts
    Curried(..)
  , toCurried, fromCurried, applied, unapplied
  , adjointToCurried, curriedToAdjoint
  , composedAdjointToCurried, curriedToComposedAdjoint
  , liftCurried, lowerCurried, rap
  ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Data.Functor.Adjunction
import Data.Functor.Day
import Data.Functor.Identity

newtype Curried g h a =
  Curried { runCurried :: forall r. g (a -> r) -> h r }

instance Functor g => Functor (Curried g h) where
  fmap f (Curried g) = Curried (g . fmap (.f))
  {-# INLINE fmap #-}

instance (Functor g, g ~ h) => Applicative (Curried g h) where
  pure a = Curried (fmap ($a))
  {-# INLINE pure #-}
  Curried mf <*> Curried ma = Curried (ma . mf . fmap (.))
  {-# INLINE (<*>) #-}

-- | The natural isomorphism between @f@ and @Curried f f@.
-- @
-- 'lowerCurried' '.' 'liftCurried' ≡ 'id'
-- 'liftCurried' '.' 'lowerCurried' ≡ 'id'
-- @
--
-- @
-- 'lowerCurried' ('liftCurried' x)     -- definition
-- 'lowerCurried' ('Curried' ('<*>' x))   -- definition
-- ('<*>' x) ('pure' 'id')          -- beta reduction
-- 'pure' 'id' '<*>' x              -- Applicative identity law
-- x
-- @
liftCurried :: Applicative f => f a -> Curried f f a
liftCurried fa = Curried (<*> fa)
{-# INLINE liftCurried #-}

-- | Lower 'Curried' by applying 'pure' 'id' to the continuation.
--
-- See 'liftCurried'.
lowerCurried :: Applicative f => Curried f g a -> g a
lowerCurried (Curried f) = f (pure id)
{-# INLINE lowerCurried #-}

-- | Indexed applicative composition of right Kan lifts.
rap :: Functor f => Curried f g (a -> b) -> Curried g h a -> Curried f h b
rap (Curried mf) (Curried ma) = Curried (ma . mf . fmap (.))
{-# INLINE rap #-}

-- | This is the counit of the @Day f -| Curried f@ adjunction
applied :: Functor f => Day f (Curried f g) a -> g a
applied (Day fb (Curried fg) bca) = fg (bca <$> fb)
{-# INLINE applied #-}

-- | This is the unit of the @Day f -| Curried f@ adjunction
unapplied :: g a -> Curried f (Day f g) a
unapplied ga = Curried $ \ fab -> Day fab ga id
{-# INLINE unapplied #-}

-- | The universal property of 'Curried'
toCurried :: (forall x. Day g k x -> h x) -> k a -> Curried g h a
toCurried h ka = Curried $ \gar -> h (Day gar ka id)
{-# INLINE toCurried #-}

-- |
-- @
-- 'toCurried' . 'fromCurried' ≡ 'id'
-- 'fromCurried' . 'toCurried' ≡ 'id'
-- @
fromCurried :: Functor f => (forall a. k a -> Curried f h a) -> Day f k b -> h b
fromCurried f (Day fc kd cdb) = runCurried (f kd) (cdb <$> fc)
{-# INLINE fromCurried #-}

-- | @Curried f Identity a@ is isomorphic to the right adjoint to @f@ if one exists.
--
-- @
-- 'adjointToCurried' . 'curriedToAdjoint' ≡ 'id'
-- 'curriedToAdjoint' . 'adjointToCurried' ≡ 'id'
-- @
adjointToCurried :: Adjunction f u => u a -> Curried f Identity a
adjointToCurried ua = Curried (Identity . rightAdjunct (<$> ua))
{-# INLINE adjointToCurried #-}

-- | @Curried f Identity a@ is isomorphic to the right adjoint to @f@ if one exists.
curriedToAdjoint :: Adjunction f u => Curried f Identity a -> u a
curriedToAdjoint (Curried m) = leftAdjunct (runIdentity . m) id
{-# INLINE curriedToAdjoint #-}

-- | @Curried f h a@ is isomorphic to the post-composition of the right adjoint of @f@ onto @h@ if such a right adjoint exists.
--
-- @
-- 'curriedToComposedAdjoint' . 'composedAdjointToCurried' ≡ 'id'
-- 'composedAdjointToCurried' . 'curriedToComposedAdjoint' ≡ 'id'
-- @

curriedToComposedAdjoint :: Adjunction f u => Curried f h a -> u (h a)
curriedToComposedAdjoint (Curried m) = leftAdjunct m id
{-# INLINE curriedToComposedAdjoint #-}

-- | @Curried f h a@ is isomorphic to the post-composition of the right adjoint of @f@ onto @h@ if such a right adjoint exists.
composedAdjointToCurried :: (Functor h, Adjunction f u) => u (h a) -> Curried f h a
composedAdjointToCurried uha = Curried $ rightAdjunct (\b -> fmap b <$> uha)
{-# INLINE composedAdjointToCurried #-}

