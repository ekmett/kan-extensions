{-# LANGUAGE RankNTypes, GADTs #-}
module Data.Functor.Contravariant.Rift where

import Control.Arrow
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
-- * Curried contravariant Day convolution / right kan lift

newtype Rift g h a = Rift { runRift :: forall b c. (b -> (a, c)) -> g c -> h b }

instance Contravariant (Rift g h) where
  contramap f (Rift m) = Rift $ \bac -> m (first f . bac)

instance (Contravariant g, g ~ h) => Divisible (Rift g h) where
  divide f (Rift g) (Rift h) = Rift $ \bac gc -> g 

{-
Rift.hs:15:50:
    Found hole ‘_heh’ with type: h b1
    Where: ‘h’ is a rigid type variable bound by
               the instance declaration at Rift.hs:14:10
           ‘b1’ is a rigid type variable bound by
                a type expected by the context: (b1 -> (a, c1)) -> g c1 -> h b1
                at Rift.hs:15:32
    Relevant bindings include
      gc :: g c1 (bound at Rift.hs:15:44)
      bac :: b1 -> (a, c1) (bound at Rift.hs:15:40)
      h :: forall b c1. (b -> (c, c1)) -> g c1 -> h b
        (bound at Rift.hs:15:27)
      g :: forall b1 c. (b1 -> (b, c)) -> g c -> h b1
        (bound at Rift.hs:15:18)
      f :: a -> (b, c) (bound at Rift.hs:15:10)
      divide :: (a -> (b, c)) -> Rift g h b -> Rift g h c -> Rift g h a
        (bound at Rift.hs:15:3)
    In the expression: _heh
    In the second argument of ‘($)’, namely ‘\ bac gc -> _heh’
    In the expression: Rift $ \ bac gc -> _heh

-}
