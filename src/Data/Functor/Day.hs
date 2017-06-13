{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014-2016 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- Eitan Chatav first introduced me to this construction
--
-- The Day convolution of two covariant functors is a covariant functor.
--
-- Day convolution is usually defined in terms of contravariant functors,
-- however, it just needs a monoidal category, and Hask^op is also monoidal.
--
-- Day convolution can be used to nicely describe monoidal functors as monoid
-- objects w.r.t this product.
--
-- <http://ncatlab.org/nlab/show/Day+convolution>
----------------------------------------------------------------------------

module Data.Functor.Day
  ( Day(..)
  , day
  , dap
  , assoc, disassoc
  , swapped
  , intro1, intro2
  , elim1, elim2
  , trans1, trans2
  , cayley, dayley
  ) where

import Control.Applicative
import Control.Category
import Control.Comonad
import Control.Comonad.Trans.Class
import Data.Distributive
import Data.Profunctor.Cayley (Cayley(..))
import Data.Profunctor.Composition (Procompose(..))
import Data.Functor.Identity
import Data.Functor.Rep
#ifdef __GLASGOW_HASKELL__
import Data.Typeable
#endif
import Prelude hiding (id,(.))

-- | The Day convolution of two covariant functors.
data Day f g a = forall b c. Day (f b) (g c) (b -> c -> a)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
  deriving Typeable
#endif

-- | Construct the Day convolution
day :: f (a -> b) -> g a -> Day f g b
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
dayTyCon = mkTyCon3 "contravariant" "Data.Functor.Day" "Day"
#else
dayTyCon = mkTyCon "Data.Functor.Day.Day"
#endif

#endif

instance Functor (Day f g) where
  fmap f (Day fb gc bca) = Day fb gc $ \b c -> f (bca b c)

instance (Applicative f, Applicative g) => Applicative (Day f g) where
  pure x = Day (pure ()) (pure ()) (\_ _ -> x)
  (Day fa fb u) <*> (Day gc gd v) =
    Day ((,) <$> fa <*> gc) ((,) <$> fb <*> gd)
        (\(a,c) (b,d) -> u a b (v c d))

instance (Representable f, Representable g) => Distributive (Day f g) where
  distribute f = Day (tabulate id) (tabulate id) $ \x y ->
    fmap (\(Day m n o) -> o (index m x) (index n y)) f

  collect g f = Day (tabulate id) (tabulate id) $ \x y ->
    fmap (\q -> case g q of Day m n o -> o (index m x) (index n y)) f

instance (Representable f, Representable g) => Representable (Day f g) where
  type Rep (Day f g) = (Rep f, Rep g)
  tabulate f = Day (tabulate id) (tabulate id) (curry f)
  index (Day m n o) (x,y) = o (index m x) (index n y)

instance (Comonad f, Comonad g) => Comonad (Day f g) where
  extract (Day fb gc bca) = bca (extract fb) (extract gc)
  duplicate (Day fb gc bca) = Day (duplicate fb) (duplicate gc) (\fb' gc' -> Day fb' gc' bca)

instance (ComonadApply f, ComonadApply g) => ComonadApply (Day f g) where
  Day fa fb u <@> Day gc gd v =
    Day ((,) <$> fa <@> gc) ((,) <$> fb <@> gd)
        (\(a,c) (b,d) -> u a b (v c d))

instance Comonad f => ComonadTrans (Day f) where
  lower (Day fb gc bca) = bca (extract fb) <$> gc

-- | Day convolution provides a monoidal product. The associativity
-- of this monoid is witnessed by 'assoc' and 'disassoc'.
--
-- @
-- 'assoc' . 'disassoc' = 'id'
-- 'disassoc' . 'assoc' = 'id'
-- 'fmap' f '.' 'assoc' = 'assoc' '.' 'fmap' f
-- @
assoc :: Day f (Day g h) a -> Day (Day f g) h a
assoc (Day fb (Day gd he dec) bca) = Day (Day fb gd (,)) he $
  \ (b,d) e -> bca b (dec d e)

-- | Day convolution provides a monoidal product. The associativity
-- of this monoid is witnessed by 'assoc' and 'disassoc'.
--
-- @
-- 'assoc' . 'disassoc' = 'id'
-- 'disassoc' . 'assoc' = 'id'
-- 'fmap' f '.' 'disassoc' = 'disassoc' '.' 'fmap' f
-- @
disassoc :: Day (Day f g) h a -> Day f (Day g h) a
disassoc (Day (Day fb gc bce) hd eda) = Day fb (Day gc hd (,)) $ \ b (c,d) ->
  eda (bce b c) d

-- | The monoid for 'Day' convolution on the cartesian monoidal structure is symmetric.
--
-- @
-- 'fmap' f '.' 'swapped' = 'swapped' '.' 'fmap' f
-- @
swapped :: Day f g a -> Day g f a
swapped (Day fb gc abc) = Day gc fb (flip abc)

-- | 'Identity' is the unit of 'Day' convolution
--
-- @
-- 'intro1' '.' 'elim1' = 'id'
-- 'elim1' '.' 'intro1' = 'id'
-- @
intro1 :: f a -> Day Identity f a
intro1 fa = Day (Identity ()) fa $ \_ a -> a

-- | 'Identity' is the unit of 'Day' convolution
--
-- @
-- 'intro2' '.' 'elim2' = 'id'
-- 'elim2' '.' 'intro2' = 'id'
-- @
intro2 :: f a -> Day f Identity a
intro2 fa = Day fa (Identity ()) const

-- | 'Identity' is the unit of 'Day' convolution
--
-- @
-- 'intro1' '.' 'elim1' = 'id'
-- 'elim1' '.' 'intro1' = 'id'
-- @
elim1 :: Functor f => Day Identity f a -> f a
elim1 (Day (Identity b) fc bca) = bca b <$> fc

-- | 'Identity' is the unit of 'Day' convolution
--
-- @
-- 'intro2' '.' 'elim2' = 'id'
-- 'elim2' '.' 'intro2' = 'id'
-- @
elim2 :: Functor f => Day f Identity a -> f a
elim2 (Day fb (Identity c) bca) = flip bca c <$> fb

-- | Collapse via a monoidal functor.
--
-- @ 
-- 'dap' ('day' f g) = f '<*>' g
-- @
dap :: Applicative f => Day f f a -> f a
dap (Day fb fc abc) = liftA2 abc fb fc

-- | Apply a natural transformation to the left-hand side of a Day convolution.
--
-- This respects the naturality of the natural transformation you supplied:
--
-- @
-- 'fmap' f '.' 'trans1' fg = 'trans1' fg '.' 'fmap' f
-- @
trans1 :: (forall x. f x -> g x) -> Day f h a -> Day g h a
trans1 fg (Day fb hc bca) = Day (fg fb) hc bca

-- | Apply a natural transformation to the right-hand side of a Day convolution.
--
-- This respects the naturality of the natural transformation you supplied:
--
-- @
-- 'fmap' f '.' 'trans2' fg = 'trans2' fg '.' 'fmap' f
-- @
trans2 :: (forall x. g x -> h x) -> Day f g a -> Day f h a
trans2 gh (Day fb gc bca) = Day fb (gh gc) bca

cayley :: Procompose (Cayley f p) (Cayley g q) a b -> Cayley (Day f g) (Procompose p q) a b
cayley (Procompose (Cayley p) (Cayley q)) = Cayley $ Day p q Procompose

-- | Proposition 4.1 from Pastro and Street
dayley :: Category p => Procompose (Cayley f p) (Cayley g p) a b -> Cayley (Day f g) p a b
dayley (Procompose (Cayley p) (Cayley q)) = Cayley $ Day p q (.)
