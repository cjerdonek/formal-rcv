module List where

import qualified Prelude
import qualified Datatypes


existsb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
existsb f l =
  case l of {
   [] -> Prelude.False;
   (:) a l0 -> Datatypes.orb (f a) (existsb f l0)}

forallb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
forallb f l =
  case l of {
   [] -> Prelude.True;
   (:) a l0 -> Datatypes.andb (f a) (forallb f l0)}

