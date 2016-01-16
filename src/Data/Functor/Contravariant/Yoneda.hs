{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
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
----------------------------------------------------------------------------
module Data.Functor.Contravariant.Yoneda
  ( Yoneda(..)
  , liftYoneda, lowerYoneda
  ) where

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Adjunction
import Data.Functor.Contravariant.Rep

-- | Yoneda embedding for a presheaf
newtype Yoneda f a = Yoneda { runYoneda :: forall r. (r -> a) -> f r }

-- |
--
-- @
-- 'liftYoneda' . 'lowerYoneda' ≡ 'id'
-- 'lowerYoneda' . 'liftYoneda' ≡ 'id'
-- @

liftYoneda :: Contravariant f => f a -> Yoneda f a
liftYoneda fa = Yoneda $ \ra -> contramap ra fa
{-# INLINE liftYoneda #-}

lowerYoneda :: Yoneda f a -> f a
lowerYoneda f = runYoneda f id
{-# INLINE lowerYoneda #-}

instance Contravariant (Yoneda f) where
  contramap ab (Yoneda m) = Yoneda (m . fmap ab)
  {-# INLINE contramap #-}

instance Representable f => Representable (Yoneda f) where
  type Rep (Yoneda f) = Rep f
  tabulate = liftYoneda . tabulate
  {-# INLINE tabulate #-}
  index m a = index (lowerYoneda m) a
  {-# INLINE index #-}
  contramapWithRep beav = liftYoneda . contramapWithRep beav . lowerYoneda
  {-# INLINE contramapWithRep #-}

instance Adjunction f g => Adjunction (Yoneda f) (Yoneda g) where
  leftAdjunct f = liftYoneda . leftAdjunct (lowerYoneda . f)
  {-# INLINE leftAdjunct #-}
  rightAdjunct f = liftYoneda . rightAdjunct (lowerYoneda . f)
  {-# INLINE rightAdjunct #-}
