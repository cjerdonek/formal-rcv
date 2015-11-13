module Peano where

import qualified Prelude
import qualified Datatypes


plus :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
plus n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S p -> Datatypes.S (plus p m)}

nat_iter :: Datatypes.Coq_nat -> (a1 -> a1) -> a1 -> a1
nat_iter n f x =
  case n of {
   Datatypes.O -> x;
   Datatypes.S n' -> f (nat_iter n' f x)}

