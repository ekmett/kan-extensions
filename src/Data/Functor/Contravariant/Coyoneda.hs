{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013-2016 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, TFs, MPTCs
--
-- The co-Yoneda lemma for presheafs states that @f@ is naturally isomorphic to @'Coyoneda' f@.
--
----------------------------------------------------------------------------
module Data.Functor.Contravariant.Coyoneda
  ( Coyoneda(..)
  , liftCoyoneda
  , lowerCoyoneda
  , hoistCoyoneda
  ) where

import Control.Arrow
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Adjunction
import Data.Functor.Contravariant.Rep


-- | A 'Contravariant' functor (aka presheaf) suitable for Yoneda reduction.
--
-- <http://ncatlab.org/nlab/show/Yoneda+reduction>
data Coyoneda f a where
  Coyoneda :: (a -> b) -> f b -> Coyoneda f a

instance Contravariant (Coyoneda f) where
  contramap f (Coyoneda g m) = Coyoneda (g.f) m
  {-# INLINE contramap #-}

instance Representable f => Representable (Coyoneda f) where
  type Rep (Coyoneda f) = Rep f
  tabulate = liftCoyoneda . tabulate
  {-# INLINE tabulate #-}
  index (Coyoneda ab fb) a = index fb (ab a)
  {-# INLINE index #-}
  contramapWithRep beav (Coyoneda ac fc) = Coyoneda (left ac . beav) (contramapWithRep id fc)
  {-# INLINE contramapWithRep #-}

instance Adjunction f g => Adjunction (Coyoneda f) (Coyoneda g) where
  leftAdjunct f = liftCoyoneda . leftAdjunct (lowerCoyoneda . f)
  {-# INLINE leftAdjunct #-}
  rightAdjunct f = liftCoyoneda . rightAdjunct (lowerCoyoneda . f)
  {-# INLINE rightAdjunct #-}

-- | Coyoneda "expansion" of a presheaf
--
-- @
-- 'liftCoyoneda' . 'lowerCoyoneda' ≡ 'id'
-- 'lowerCoyoneda' . 'liftCoyoneda' ≡ 'id'
-- @
liftCoyoneda :: f a -> Coyoneda f a
liftCoyoneda = Coyoneda id
{-# INLINE liftCoyoneda #-}

-- | Coyoneda reduction on a presheaf
lowerCoyoneda :: Contravariant f => Coyoneda f a -> f a
lowerCoyoneda (Coyoneda f m) = contramap f m
{-# INLINE lowerCoyoneda #-}

-- | Lift a natural transformation from @f@ to @g@ to a natural transformation
-- from @Coyoneda f@ to @Coyoneda g@.
hoistCoyoneda :: (forall a. f a -> g a) -> (Coyoneda f b -> Coyoneda g b)
hoistCoyoneda f (Coyoneda g x) = Coyoneda g (f x)
{-# INLINE hoistCoyoneda #-}
