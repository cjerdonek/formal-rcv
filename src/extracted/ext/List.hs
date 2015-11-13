module List where

import qualified Prelude
import qualified Datatypes


map :: (a1 -> a2) -> ([] a1) -> [] a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

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

filter :: (a1 -> Prelude.Bool) -> ([] a1) -> [] a1
filter f l =
  case l of {
   [] -> [];
   (:) x l0 ->
    case f x of {
     Prelude.True -> (:) x (filter f l0);
     Prelude.False -> filter f l0}}

