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
module Data.Functor.KanExtension where

import Data.Functor.Identity
import Data.Functor.Adjunction
import Data.Functor.Composition
import Data.Functor.Apply
import Control.Applicative

newtype Ran g h a = Ran { runRan :: forall b. (a -> g b) -> h b }

instance Functor (Ran g h) where
  fmap f m = Ran (\k -> runRan m (k . f))
 
-- | 'toRan' and 'fromRan' witness a higher kinded adjunction. from @(`'Compose'` g)@ to @'Ran' g@
toRan :: Functor k => (forall a. k (g a) -> h a) -> k b -> Ran g h b
toRan s t = Ran (s . flip fmap t)

fromRan :: (forall a. k a -> Ran g h a) -> k (g b) -> h b
fromRan s = flip runRan id . s

composeRan :: Composition compose => Ran f (Ran g h) a -> Ran (compose f g) h a
composeRan r = Ran (\f -> runRan (runRan r (decompose . f)) id)

decomposeRan :: (Composition compose, Functor f) => Ran (compose f g) h a -> Ran f (Ran g h) a
decomposeRan r = Ran (\f -> Ran (\g -> runRan r (compose . fmap g . f)))

adjointToRan :: Adjunction f g => f a -> Ran g Identity a
adjointToRan f = Ran (\a -> Identity $ rightAdjunct a f)

ranToAdjoint :: Adjunction f g => Ran g Identity a -> f a
ranToAdjoint r = runIdentity (runRan r unit)

ranToComposedAdjoint :: Adjunction f g => Ran g h a -> h (f a)
ranToComposedAdjoint r = runRan r unit

composedAdjointToRan :: (Adjunction f g, Functor h) => h (f a) -> Ran g h a
composedAdjointToRan f = Ran (\a -> fmap (rightAdjunct a) f)

data Lan g h a where
  Lan :: (g b -> a) -> h b -> Lan g h a

-- 'fromLan' and 'toLan' witness a (higher kinded) adjunction between @'Lan' g@ and @(`Compose` g)@
toLan :: Functor f => (forall a. h a -> f (g a)) -> Lan g h b -> f b
toLan s (Lan f v) = fmap f (s v)

fromLan :: (forall a. Lan g h a -> f a) -> h b -> f (g b)
fromLan s = s . Lan id

instance Functor (Lan f g) where
  fmap f (Lan g h) = Lan (f . g) h

instance (Functor g, Apply h) => Apply (Lan g h) where
  Lan kxf x <.> Lan kya y =
    Lan (\k -> kxf (fmap fst k) (kya (fmap snd k))) ((,) <$> x <.> y)

instance (Functor g, Applicative h) => Applicative (Lan g h) where
  pure a = Lan (const a) (pure ())
  Lan kxf x <*> Lan kya y =
    Lan (\k -> kxf (fmap fst k) (kya (fmap snd k))) (liftA2 (,) x y)

adjointToLan :: Adjunction f g => g a -> Lan f Identity a
adjointToLan = Lan counit . Identity

lanToAdjoint :: Adjunction f g => Lan f Identity a -> g a
lanToAdjoint (Lan f v) = leftAdjunct f (runIdentity v)

-- | 'lanToComposedAdjoint' and 'composedAdjointToLan' witness the natural isomorphism between @Lan f h@ and @Compose h g@ given @f -| g@
lanToComposedAdjoint :: (Functor h, Adjunction f g) => Lan f h a -> h (g a)
lanToComposedAdjoint (Lan f v) = fmap (leftAdjunct f) v

composedAdjointToLan :: Adjunction f g => h (g a) -> Lan f h a
composedAdjointToLan = Lan counit

-- | 'composeLan' and 'decomposeLan' witness the natural isomorphism from @Lan f (Lan g h)@ and @Lan (f `o` g) h@
composeLan :: (Composition compose, Functor f) => Lan f (Lan g h) a -> Lan (compose f g) h a
composeLan (Lan f (Lan g h)) = Lan (f . fmap g . decompose) h

decomposeLan :: Composition compose => Lan (compose f g) h a -> Lan f (Lan g h) a
decomposeLan (Lan f h) = Lan (f . compose) (Lan id h)

