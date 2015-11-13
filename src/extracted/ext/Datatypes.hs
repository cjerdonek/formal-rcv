module Datatypes where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> b2}

negb :: Prelude.Bool -> Prelude.Bool
negb b =
  case b of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

data Coq_nat =
   O
 | S Coq_nat

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x y -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) x y -> y}

length :: ([] a1) -> Coq_nat
length l =
  case l of {
   [] -> O;
   (:) y l' -> S (length l')}

app :: ([] a1) -> ([] a1) -> [] a1
app l m =
  case l of {
   [] -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Coq_comparison =
   Eq
 | Lt
 | Gt

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

coq_CompareSpec2Type :: Coq_comparison -> CompareSpecT
coq_CompareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

coq_CompSpec2Type :: a1 -> a1 -> Coq_comparison -> CompSpecT a1
coq_CompSpec2Type x y c =
  coq_CompareSpec2Type c

