module EqNat where

import qualified Prelude
import qualified Datatypes


beq_nat :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
beq_nat n m =
  case n of {
   Datatypes.O ->
    case m of {
     Datatypes.O -> Prelude.True;
     Datatypes.S n0 -> Prelude.False};
   Datatypes.S n1 ->
    case m of {
     Datatypes.O -> Prelude.False;
     Datatypes.S m1 -> beq_nat n1 m1}}

