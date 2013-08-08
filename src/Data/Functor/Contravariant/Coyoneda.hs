{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
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
  ) where

import Control.Arrow
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Adjunction
import Data.Functor.Contravariant.Representable

type instance Value (Coyoneda f) = Value f

-- | A 'Contravariant' functor (aka presheaf) suitable for Yoneda reduction.
--
-- <http://ncatlab.org/nlab/show/Yoneda+reduction>
data Coyoneda f a where
  Coyoneda :: (a -> b) -> f b -> Coyoneda f a

instance Contravariant (Coyoneda f) where
  contramap f (Coyoneda g m) = Coyoneda (g.f) m
  {-# INLINE contramap #-}

instance Valued f => Valued (Coyoneda f) where
  contramapWithValue beav (Coyoneda ac fc) = Coyoneda (left ac . beav) (contramapWithValue id fc)
  {-# INLINE contramapWithValue #-}

instance Coindexed f => Coindexed (Coyoneda f) where
  coindex (Coyoneda ab fb) a = coindex fb (ab a)
  {-# INLINE coindex #-}

instance Representable f => Representable (Coyoneda f) where
  contrarep = liftCoyoneda . contrarep
  {-# INLINE contrarep #-}

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
