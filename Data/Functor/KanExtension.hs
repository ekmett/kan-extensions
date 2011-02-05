{-# LANGUAGE Rank2Types, GADTs #-}
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

newtype Ran g h a = Ran { runRan :: forall b. (a -> g b) -> h b }

instance Functor (Ran g h) where
  fmap f m = Ran (\k -> runRan m (k . f))
 
-- | 'toRan' and 'fromRan' witness a higher kinded adjunction. from @(`'Compose'` g)@ to @'Ran' g@
toRan :: (Composition compose, Functor k) => (forall a. compose k g a -> h a) -> k b -> Ran g h b
toRan s t = Ran (s . compose . flip fmap t)

fromRan :: Composition compose => (forall a. k a -> Ran g h a) -> compose k g b -> h b
fromRan s = flip runRan id . s . decompose

composeRan :: Composition compose => Ran f (Ran g h) a -> Ran (compose f g) h a
composeRan r = Ran (\f -> runRan (runRan r (decompose . f)) id)

decomposeRan :: (Composition compose, Functor f) => Ran (compose f g) h a -> Ran f (Ran g h) a
decomposeRan r = Ran (\f -> Ran (\g -> runRan r (compose . fmap g . f)))

adjointToRan :: Adjunction f g => f a -> Ran g Identity a
adjointToRan f = Ran (\a -> Identity $ rightAdjunct a f)

ranToAdjoint :: Adjunction f g => Ran g Identity a -> f a
ranToAdjoint r = runIdentity (runRan r unit)

ranToComposedAdjoint :: (Composition compose, Adjunction f g) => Ran g h a -> compose h f a
ranToComposedAdjoint r = compose (runRan r unit)

composedAdjointToRan :: (Composition compose, Adjunction f g, Functor h) => compose h f a -> Ran g h a
composedAdjointToRan f = Ran (\a -> fmap (rightAdjunct a) (decompose f))

data Lan g h a where
  Lan :: (g b -> a) -> h b -> Lan g h a

-- 'fromLan' and 'toLan' witness a (higher kinded) adjunction between @'Lan' g@ and @(`Compose` g)@
toLan :: (Composition compose, Functor f) => (forall a. h a -> compose f g a) -> Lan g h b -> f b
toLan s (Lan f v) = fmap f . decompose $ s v

fromLan :: (Composition compose) => (forall a. Lan g h a -> f a) -> h b -> compose f g b
fromLan s = compose . s . Lan id

instance Functor (Lan f g) where
  fmap f (Lan g h) = Lan (f . g) h

adjointToLan :: Adjunction f g => g a -> Lan f Identity a
adjointToLan = Lan counit . Identity

lanToAdjoint :: Adjunction f g => Lan f Identity a -> g a
lanToAdjoint (Lan f v) = leftAdjunct f (runIdentity v)

-- | 'lanToComposedAdjoint' and 'composedAdjointToLan' witness the natural isomorphism between @Lan f h@ and @Compose h g@ given @f -| g@
lanToComposedAdjoint :: (Composition compose, Functor h, Adjunction f g) => Lan f h a -> compose h g a
lanToComposedAdjoint (Lan f v) = compose (fmap (leftAdjunct f) v)

composedAdjointToLan :: Composition compose => Adjunction f g => compose h g a -> Lan f h a
composedAdjointToLan = Lan counit . decompose

-- | 'composeLan' and 'decomposeLan' witness the natural isomorphism from @Lan f (Lan g h)@ and @Lan (f `o` g) h@
composeLan :: (Composition compose, Functor f) => Lan f (Lan g h) a -> Lan (compose f g) h a
composeLan (Lan f (Lan g h)) = Lan (f . fmap g . decompose) h

decomposeLan :: Composition compose => Lan (compose f g) h a -> Lan f (Lan g h) a
decomposeLan (Lan f h) = Lan (f . compose) (Lan id h)

