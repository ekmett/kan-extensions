{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Rank2Types #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
#endif
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ <= 707
{-# LANGUAGE KindSignatures #-}
#endif
#if __GLASGOW_HASKELL__ >= 702 && __GLASGOW_HASKELL__ < 710
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013-2016 Edward Kmett, Gershom Bazerman and Derek Elkins
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- The Day convolution of two contravariant functors is a contravariant
-- functor.
--
-- <http://ncatlab.org/nlab/show/Day+convolution>
----------------------------------------------------------------------------

module Data.Functor.Contravariant.Day
  ( Day(..)
  , day
  , runDay
  , assoc, disassoc
  , swapped
  , intro1, intro2
  , day1, day2
  , diag
  , trans1, trans2
  ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Rep
import Data.Proxy
import Data.Tuple (swap)
#ifdef __GLASGOW_HASKELL__
import Data.Typeable
#endif

-- | The Day convolution of two contravariant functors.
data Day f g a = forall b c. Day (f b) (g c) (a -> (b, c))
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
  deriving Typeable
#endif

-- | Construct the Day convolution
--
-- @
-- 'day1' ('day' f g) = f
-- 'day2' ('day' f g) = g
-- @
day :: f a -> g b -> Day f g (a, b)
day fa gb = Day fa gb id

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 707
instance (Typeable1 f, Typeable1 g) => Typeable1 (Day f g) where
    typeOf1 tfga = mkTyConApp dayTyCon [typeOf1 (fa tfga), typeOf1 (ga tfga)]
        where fa :: t f (g :: * -> *) a -> f a
              fa = undefined
              ga :: t (f :: * -> *) g a -> g a
              ga = undefined

dayTyCon :: TyCon
#if MIN_VERSION_base(4,4,0)
dayTyCon = mkTyCon3 "contravariant" "Data.Functor.Contravariant.Day" "Day"
#else
dayTyCon = mkTyCon "Data.Functor.Contravariant.Day.Day"
#endif

#endif

instance Contravariant (Day f g) where
  contramap f (Day fb gc abc) = Day fb gc (abc . f)

instance (Representable f, Representable g) => Representable (Day f g) where
  type Rep (Day f g) = (Rep f, Rep g)

  tabulate a2fg = Day (tabulate fst) (tabulate snd) $ \a -> let b = a2fg a in (b,b)

  index (Day fb gc abc) a = case abc a of
    (b, c) -> (index fb b, index gc c)
  {-# INLINE index #-}

  contramapWithRep d2eafg (Day fb gc abc) = Day (contramapWithRep id fb) (contramapWithRep id gc) $ \d -> case d2eafg d of
    Left a -> case abc a of
      (b, c) -> (Left b, Left c)
    Right (vf, vg) -> (Right vf, Right vg)
  {-# INLINE tabulate #-}


-- | Break apart the Day convolution of two contravariant functors.
runDay :: (Contravariant f, Contravariant g) => Day f g a -> (f a, g a)
runDay (Day fb gc abc) =
  ( contramap (fst . abc) fb
  , contramap (snd . abc) gc
  )

-- | Day convolution provides a monoidal product. The associativity
-- of this monoid is witnessed by 'assoc' and 'disassoc'.
--
-- @
-- 'assoc' . 'disassoc' = 'id'
-- 'disassoc' . 'assoc' = 'id'
-- 'contramap' f '.' 'assoc' = 'assoc' '.' 'contramap' f
-- @
assoc :: Day f (Day g h) a -> Day (Day f g) h a
assoc (Day fb (Day gd he cde) abc) = Day (Day fb gd id) he $ \a ->
  case cde <$> abc a of
    (b, (d, e)) -> ((b, d), e)

-- | Day convolution provides a monoidal product. The associativity
-- of this monoid is witnessed by 'assoc' and 'disassoc'.
--
-- @
-- 'assoc' . 'disassoc' = 'id'
-- 'disassoc' . 'assoc' = 'id'
-- 'contramap' f '.' 'disassoc' = 'disassoc' '.' 'contramap' f
-- @
disassoc :: Day (Day f g) h a -> Day f (Day g h) a
disassoc (Day (Day fd ge bde) hc abc) = Day fd (Day ge hc id) $ \a ->
  case abc a of
    (b, c) -> case bde b of
      (d, e) -> (d, (e, c))

-- | The monoid for Day convolution /in Haskell/ is symmetric.
--
-- @
-- 'contramap' f '.' 'swapped' = 'swapped' '.' 'contramap' f
-- @
swapped :: Day f g a -> Day g f a
swapped (Day fb gc abc) = Day gc fb (swap . abc)

-- | Proxy serves as the unit of Day convolution.
--
-- @
-- 'day1' '.' 'intro1' = 'id'
-- 'contramap' f '.' 'intro1' = 'intro1' '.' 'contramap' f
-- @
intro1 :: f a -> Day Proxy f a
intro1 fa = Day Proxy fa $ \a -> ((),a)

-- | Proxy serves as the unit of Day convolution.
--
-- @
-- 'day2' '.' 'intro2' = 'id'
-- 'contramap' f '.' 'intro2' = 'intro2' '.' 'contramap' f
-- @
intro2 :: f a -> Day f Proxy a
intro2 fa = Day fa Proxy $ \a -> (a,())

-- | In Haskell we can do general purpose elimination, but in a more general setting
-- it is only possible to eliminate the unit.
--
-- @
-- 'day1' '.' 'intro1' = 'id'
-- 'day1' = 'fst' '.' 'runDay'
-- 'contramap' f '.' 'day1' = 'day1' '.' 'contramap' f
-- @
day1 :: Contravariant f => Day f g a -> f a
day1 (Day fb _ abc) = contramap (fst . abc) fb

-- | In Haskell we can do general purpose elimination, but in a more general setting
-- it is only possible to eliminate the unit.
-- @
-- 'day2' '.' 'intro2' = 'id'
-- 'day2' = 'snd' '.' 'runDay'
-- 'contramap' f '.' 'day2' = 'day2' '.' 'contramap' f
-- @
day2 :: Contravariant g => Day f g a -> g a
day2 (Day _ gc abc) = contramap (snd . abc) gc

-- | Diagonalize the Day convolution:
--
-- @
-- 'day1' '.' 'diag' = 'id'
-- 'day2' '.' 'diag' = 'id'
-- 'runDay' '.' 'diag' = \a -> (a,a)
-- 'contramap' f . 'diag' = 'diag' . 'contramap' f
-- @

diag :: f a -> Day f f a
diag fa = Day fa fa $ \a -> (a,a)

-- | Apply a natural transformation to the left-hand side of a Day convolution.
--
-- This respects the naturality of the natural transformation you supplied:
--
-- @
-- 'contramap' f '.' 'trans1' fg = 'trans1' fg '.' 'contramap' f
-- @
trans1 :: (forall x. f x -> g x) -> Day f h a -> Day g h a
trans1 fg (Day fb hc abc) = Day (fg fb) hc abc

-- | Apply a natural transformation to the right-hand side of a Day convolution.
--
-- This respects the naturality of the natural transformation you supplied:
--
-- @
-- 'contramap' f '.' 'trans2' fg = 'trans2' fg '.' 'contramap' f
-- @
trans2 :: (forall x. g x -> h x) -> Day f g a -> Day f h a
trans2 gh (Day fb gc abc) = Day fb (gh gc) abc
