module NPeano where

import qualified Prelude
import qualified Datatypes


leb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
leb n m =
  case n of {
   Datatypes.O -> Prelude.True;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Prelude.False;
     Datatypes.S m' -> leb n' m'}}

ltb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
ltb n m =
  leb (Datatypes.S n) m

