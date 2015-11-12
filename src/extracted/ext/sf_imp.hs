module Sf_imp where

import qualified Prelude
import qualified List
import qualified RelDec
import qualified Sf_spec


type Coq_ballot candidate = Sf_spec.Coq_ballot candidate

type Coq_record candidate = [] ([] candidate)

eliminated :: (RelDec.RelDec a1) -> (Coq_record a1) -> a1 -> Prelude.Bool
eliminated reldec_candidate rec cand =
  List.existsb (List.existsb (RelDec.eq_dec reldec_candidate cand)) rec

next_ranking :: (RelDec.RelDec a1) -> (Coq_record a1) -> (Coq_ballot 
                a1) -> Prelude.Maybe ((,) a1 (Coq_ballot a1))
next_ranking reldec_candidate rec bal =
  case bal of {
   [] -> Prelude.Nothing;
   (:) r t ->
    case r of {
     [] -> next_ranking reldec_candidate rec t;
     (:) h l ->
      case List.forallb (RelDec.eq_dec reldec_candidate h) l of {
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

