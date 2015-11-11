module Sf_imp_tests where

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

existsb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
existsb f l =
  case l of {
   [] -> Prelude.False;
   (:) a l0 -> orb (f a) (existsb f l0)}

forallb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
forallb f l =
  case l of {
   [] -> Prelude.True;
   (:) a l0 -> andb (f a) (forallb f l0)}

type RankSelection candidate = [] candidate

type Ballot candidate = [] (RankSelection candidate)

type RelDec t =
  t -> t -> Prelude.Bool
  -- singleton inductive, whose constructor was Build_RelDec
  
rel_dec :: (RelDec a1) -> a1 -> a1 -> Prelude.Bool
rel_dec relDec =
  relDec

eq_dec :: (RelDec a1) -> a1 -> a1 -> Prelude.Bool
eq_dec eD =
  rel_dec eD

type Ballot0 candidate = Ballot candidate

type Record candidate = [] ([] candidate)

eliminated :: (RelDec a1) -> (Record a1) -> a1 -> Prelude.Bool
eliminated reldec_candidate rec cand =
  existsb (existsb (eq_dec reldec_candidate cand)) rec

next_ranking :: (RelDec a1) -> (Record a1) -> (Ballot0 a1) -> Prelude.Maybe
                ((,) a1 (Ballot0 a1))
next_ranking reldec_candidate rec bal =
  case bal of {
   [] -> Prelude.Nothing;
   (:) r t ->
    case r of {
     [] -> next_ranking reldec_candidate rec t;
     (:) h l ->
      case forallb (eq_dec reldec_candidate h) l of {
       Prelude.True ->
        case eliminated reldec_candidate rec h of {
         Prelude.True -> next_ranking reldec_candidate rec t;
         Prelude.False -> Prelude.Just ((,) h bal)};
       Prelude.False -> Prelude.Nothing}}}

drop_none :: ([] (Prelude.Maybe a1)) -> [] a1
drop_none l =
  case l of {
   [] -> [];
   (:) o t ->
    case o of {
     Prelude.Just x -> (:) x (drop_none t);
     Prelude.Nothing -> drop_none t}}

type T = Prelude.Int

prop_drop_none_keeps :: ([] (Prelude.Maybe T)) -> T -> Prelude.Bool
prop_drop_none_keeps l i =
  (Prelude.==) (existsb ((Prelude.==) (Prelude.Just i)) l)
    (existsb ((Prelude.==) i) (drop_none l))

prop_next_ranking_contains :: (Record T) -> (Ballot0 T) -> Prelude.Bool
prop_next_ranking_contains rec bal =
  case next_ranking (Prelude.==) rec bal of {
   Prelude.Just p ->
    case p of {
     (,) c b -> existsb (existsb ((Prelude.==) c)) bal};
   Prelude.Nothing -> Prelude.True}

prop_next_ranking_not_eliminated :: (Record T) -> (Ballot0 T) -> Prelude.Bool
prop_next_ranking_not_eliminated rec bal =
  case next_ranking (Prelude.==) rec bal of {
   Prelude.Just p ->
    case p of {
     (,) c b -> negb (eliminated (Prelude.==) rec c)};
   Prelude.Nothing -> Prelude.True}

is_overvote :: (Record T) -> (Ballot0 T) -> Prelude.Bool
is_overvote rec b =
  case b of {
   [] -> Prelude.False;
   (:) r t ->
    case r of {
     [] -> is_overvote rec t;
     (:) h l ->
      case forallb (eq_dec (Prelude.==) h) l of {
       Prelude.True -> Prelude.False;
       Prelude.False -> Prelude.True}}}

prop_next_ranking_not_overvote :: (Record T) -> (Ballot0 T) -> Prelude.Bool
prop_next_ranking_not_overvote rec bal =
  case next_ranking (Prelude.==) rec bal of {
   Prelude.Just p -> negb (is_overvote rec bal);
   Prelude.Nothing -> Prelude.True}

all_props :: (,)
             ((,)
             ((,) (([] (Prelude.Maybe T)) -> T -> Prelude.Bool)
             ((Record T) -> (Ballot0 T) -> Prelude.Bool))
             ((Record T) -> (Ballot0 T) -> Prelude.Bool))
             ((Record T) -> (Ballot0 T) -> Prelude.Bool)
all_props =
  (,) ((,) ((,) prop_drop_none_keeps prop_next_ranking_contains)
    prop_next_ranking_not_eliminated) prop_next_ranking_not_overvote

