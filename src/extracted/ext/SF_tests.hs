module SF_tests where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified RelDec
import qualified SF_imp


type T = Prelude.Int

option_eq :: (a1 -> a1 -> Prelude.Bool) -> (Prelude.Maybe a1) ->
             (Prelude.Maybe a1) -> Prelude.Bool
option_eq eq a b =
  case a of {
   Prelude.Just a' ->
    case b of {
     Prelude.Just b' -> eq a' b';
     Prelude.Nothing -> Prelude.False};
   Prelude.Nothing ->
    case b of {
     Prelude.Just a0 -> Prelude.False;
     Prelude.Nothing -> Prelude.True}}

prop_drop_none_keeps :: ([] (Prelude.Maybe T)) -> T -> Prelude.Bool
prop_drop_none_keeps l i =
  (Prelude.==) (List.existsb ((Prelude.==) (Prelude.Just i)) l)
    (List.existsb ((Prelude.==) i) (SF_imp.drop_none l))

prop_next_ranking_contains :: (SF_imp.Coq_record T) -> (SF_imp.Coq_ballot 
                              T) -> Prelude.Bool
prop_next_ranking_contains rec bal =
  case SF_imp.next_ranking (Prelude.==) rec bal of {
   Prelude.Just p ->
    case p of {
     (,) c b -> List.existsb (List.existsb ((Prelude.==) c)) bal};
   Prelude.Nothing -> Prelude.True}

prop_next_ranking_not_eliminated :: (SF_imp.Coq_record T) ->
                                    (SF_imp.Coq_ballot T) -> Prelude.Bool
prop_next_ranking_not_eliminated rec bal =
  case SF_imp.next_ranking (Prelude.==) rec bal of {
   Prelude.Just p ->
    case p of {
     (,) c b -> Datatypes.negb (SF_imp.eliminated (Prelude.==) rec c)};
   Prelude.Nothing -> Prelude.True}

is_overvote :: (SF_imp.Coq_record T) -> (SF_imp.Coq_ballot T) -> Prelude.Bool
is_overvote rec b =
  case b of {
   [] -> Prelude.False;
   (:) r t ->
    case r of {
     [] -> is_overvote rec t;
     (:) h l ->
      case List.forallb (RelDec.eq_dec (Prelude.==) h) l of {
       Prelude.True -> Prelude.False;
       Prelude.False -> Prelude.True}}}

prop_next_ranking_not_overvote :: (SF_imp.Coq_record T) -> (SF_imp.Coq_ballot
                                  T) -> Prelude.Bool
prop_next_ranking_not_overvote rec bal =
  case SF_imp.next_ranking (Prelude.==) rec bal of {
   Prelude.Just p -> Datatypes.negb (is_overvote rec bal);
   Prelude.Nothing -> Prelude.True}

all_props :: (,)
             ((,)
             ((,) (([] (Prelude.Maybe T)) -> T -> Prelude.Bool)
             ((SF_imp.Coq_record T) -> (SF_imp.Coq_ballot T) -> Prelude.Bool))
             ((SF_imp.Coq_record T) -> (SF_imp.Coq_ballot T) -> Prelude.Bool))
             ((SF_imp.Coq_record T) -> (SF_imp.Coq_ballot T) -> Prelude.Bool)
all_props =
  (,) ((,) ((,) prop_drop_none_keeps prop_next_ranking_contains)
    prop_next_ranking_not_eliminated) prop_next_ranking_not_overvote

