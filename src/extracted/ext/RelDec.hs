module RelDec where

import qualified Prelude

type RelDec t =
  t -> t -> Prelude.Bool
  -- singleton inductive, whose constructor was Build_RelDec
  
rel_dec :: (RelDec a1) -> a1 -> a1 -> Prelude.Bool
rel_dec relDec =
  relDec

eq_dec :: (RelDec a1) -> a1 -> a1 -> Prelude.Bool
eq_dec eD =
  rel_dec eD

