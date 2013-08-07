{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs
--
-- Yoneda Reduction of presheafs
--
-- <http://ncatlab.org/nlab/show/Yoneda+reduction>
--
----------------------------------------------------------------------------
module Data.Functor.Contravariant.Yoneda.Reduction
  ( Yoneda(..)
  , liftYoneda
  , lowerYoneda
  ) where

import Data.Functor.Contravariant

-- | A 'Contravariant' functor (aka presheaf) suitable for Yoneda reduction.
data Yoneda f a where
  Yoneda :: (a -> b) -> f b -> Yoneda f a

instance Contravariant f => Contravariant (Yoneda f) where
  contramap f (Yoneda g m) = Yoneda (g.f) m
  {-# INLINE contramap #-}

-- | Yoneda "expansion" of a presheaf
liftYoneda :: f a -> Yoneda f a
liftYoneda = Yoneda id
{-# INLINE liftYoneda #-}

-- | Yoneda reduction on a presheaf
lowerYoneda :: Contravariant f => Yoneda f a -> f a
lowerYoneda (Yoneda f m) = contramap f m
{-# INLINE lowerYoneda #-}
