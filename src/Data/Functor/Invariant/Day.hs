{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes                #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2018 Brian Mckenna
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- The Day convolution of two invariant functors is an invariant
-- functor.
--
-- <http://ncatlab.org/nlab/show/Day+convolution>
----------------------------------------------------------------------------

module Data.Functor.Invariant.Day
  ( Day(..)
  , day
  , assoc, disassoc
  , swapped
  , intro1, intro2
  , elim1, elim2
  , trans1, trans2
  , toContravariant, toCovariant
  ) where

import qualified Data.Functor.Contravariant.Day as Contravariant
import qualified Data.Functor.Day               as Covariant
import           Data.Functor.Identity
import           Data.Functor.Invariant

-- | The Day convolution of two invariant functors.
data Day f g a = forall b c. Day (f b) (g c) (b -> c -> a) (a -> (b, c))

instance Invariant (Day f g) where
  invmap f g (Day fb gc bca abc) = Day fb gc ((f .) . bca) (abc . g)

-- | Construct the Day convolution
day :: f a -> g b -> Day f g (a, b)
day fa gb = Day fa gb (,) id

-- | Day convolution provides a monoidal product. The associativity
-- of this monoid is witnessed by 'assoc' and 'disassoc'.
--
-- @
-- 'assoc' . 'disassoc' = 'id'
-- 'disassoc' . 'assoc' = 'id'
-- 'invmap' f g '.' 'assoc' = 'assoc' '.' 'invmap' f g
-- @
assoc :: Day f (Day g h) a -> Day (Day f g) h a
assoc (Day fb (Day gd he dec cde) bca abc) = flip (Day (Day fb gd (,) id) he) f g
  where
    f a =
      let (b,c) = abc a
          (d,e) = cde c
      in ((b,d),e)
    g (b,d) e =
      bca b (dec d e)

-- | Day convolution provides a monoidal product. The associativity
-- of this monoid is witnessed by 'assoc' and 'disassoc'.
--
-- @
-- 'assoc' . 'disassoc' = 'id'
-- 'disassoc' . 'assoc' = 'id'
-- 'invmap' f g '.' 'disassoc' = 'disassoc' '.' 'invmap' f g
-- @
disassoc :: Day (Day f g) h a -> Day f (Day g h) a
disassoc (Day (Day fb gc deb bde) hd bca abc) = Day fb (Day gc hd (,) id) f g
  where
    f e (d,c) =
      bca (deb e d) c
    g a =
      let (b,c) = abc a
          (d,e) = bde b
      in (d,(e,c))

-- | The monoid for 'Day' convolution on the cartesian monoidal structure is symmetric.
--
-- @
-- 'invmap' f g '.' 'swapped' = 'swapped' '.' 'invmap' f g
-- @
swapped :: Day f g a -> Day g f a
swapped (Day fb gc bca abc) = Day gc fb (flip bca) (\a -> let (b, c) = abc a in (c, b))

-- | 'Identity' is the unit of 'Day' convolution
--
-- @
-- 'intro1' '.' 'elim1' = 'id'
-- 'elim1' '.' 'intro1' = 'id'
-- @
intro1 :: f a -> Day Identity f a
intro1 fa = Day (Identity ()) fa (\_ a -> a) ((,) ())

-- | 'Identity' is the unit of 'Day' convolution
--
-- @
-- 'intro2' '.' 'elim2' = 'id'
-- 'elim2' '.' 'intro2' = 'id'
-- @
intro2 :: f a -> Day f Identity a
intro2 fa = Day fa (Identity ()) const (flip (,) ())

-- | 'Identity' is the unit of 'Day' convolution
--
-- @
-- 'intro1' '.' 'elim1' = 'id'
-- 'elim1' '.' 'intro1' = 'id'
-- @
elim1 :: Invariant f => Day Identity f a -> f a
elim1 (Day (Identity b) fc bca abc) = invmap (bca b) (snd . abc) fc

-- | 'Identity' is the unit of 'Day' convolution
--
-- @
-- 'intro2' '.' 'elim2' = 'id'
-- 'elim2' '.' 'intro2' = 'id'
-- @
elim2 :: Invariant f => Day f Identity a -> f a
elim2 (Day fb (Identity c) bca abc) = invmap (flip bca c) (fst . abc) fb

-- | Apply a natural transformation to the left-hand side of a Day convolution.
--
-- This respects the naturality of the natural transformation you supplied:
--
-- @
-- 'invmap' f g '.' 'trans1' fg = 'trans1' fg '.' 'invmap' f g
-- @
trans1 :: (forall x. f x -> g x) -> Day f h a -> Day g h a
trans1 fg (Day fb hc bca abc) = Day (fg fb) hc bca abc

-- | Apply a natural transformation to the right-hand side of a Day convolution.
--
-- This respects the naturality of the natural transformation you supplied:
--
-- @
-- 'invmap' f g '.' 'trans2' fg = 'trans2' fg '.' 'invmap' f g
-- @
trans2 :: (forall x. g x -> h x) -> Day f g a -> Day f h a
trans2 gh (Day fb gc bca abc) = Day fb (gh gc) bca abc

-- | Drop the covariant part of the Day convolution.
toContravariant :: Day f g a -> Contravariant.Day f g a
toContravariant (Day fb gc _ abc) = Contravariant.Day fb gc abc

-- | Drop the contravariant part of the Day convolution.
toCovariant :: Day f g a -> Covariant.Day f g a
toCovariant (Day fb gc bca _) = Covariant.Day fb gc bca
