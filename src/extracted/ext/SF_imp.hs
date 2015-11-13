module SF_imp where

import qualified Prelude
import qualified BinNat
import qualified BinNums
import qualified Datatypes
import qualified EqNat
import qualified List
import qualified NPeano
import qualified RelDec
import qualified SF_spec


type Coq_rankSelection candidate = SF_spec.Coq_rankSelection candidate

type Coq_ballot candidate = SF_spec.Coq_ballot candidate

type Coq_record candidate = [] ([] candidate)

eliminated :: (RelDec.RelDec a1) -> (Coq_record a1) -> a1 -> Prelude.Bool
eliminated reldec_candidate rec cand =
  List.existsb (List.existsb (RelDec.eq_dec reldec_candidate cand)) rec

no_viable_candidates_selection :: (RelDec.RelDec a1) -> (Coq_record a1) ->
                                  (Coq_rankSelection a1) -> Prelude.Bool
no_viable_candidates_selection reldec_candidate rec sel =
  List.forallb (eliminated reldec_candidate rec) sel

no_viable_candidates :: (RelDec.RelDec a1) -> (Coq_record a1) -> (Coq_ballot
                        a1) -> Prelude.Bool
no_viable_candidates reldec_candidate rec bal =
  List.forallb (no_viable_candidates_selection reldec_candidate rec) bal

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

increment :: (RelDec.RelDec a1) -> ([] ((,) a1 BinNums.N)) -> a1 -> []
             ((,) a1 BinNums.N)
increment reldec_candidate r c =
  case r of {
   [] -> (:) ((,) c (BinNums.Npos BinNums.Coq_xH)) [];
   (:) p t ->
    case p of {
     (,) c1 n ->
      case RelDec.eq_dec reldec_candidate c1 c of {
       Prelude.True -> (:) ((,) c1
        (BinNat._N__add n (BinNums.Npos BinNums.Coq_xH))) t;
       Prelude.False -> (:) ((,) c1 n) (increment reldec_candidate t c)}}}

tabulate'' :: (RelDec.RelDec a1) -> ([] (Prelude.Maybe a1)) -> ([]
              ((,) a1 BinNums.N)) -> [] ((,) a1 BinNums.N)
tabulate'' reldec_candidate rs lc =
  case rs of {
   [] -> lc;
   (:) o t ->
    case o of {
     Prelude.Just h ->
      tabulate'' reldec_candidate t (increment reldec_candidate lc h);
     Prelude.Nothing -> tabulate'' reldec_candidate t lc}}

tabulate' :: (RelDec.RelDec a1) -> ([] (Prelude.Maybe a1)) -> []
             ((,) a1 BinNums.N)
tabulate' reldec_candidate rs =
  tabulate'' reldec_candidate rs []

cnle :: ((,) a1 BinNums.N) -> ((,) a1 BinNums.N) -> Prelude.Bool
cnle a b =
  case a of {
   (,) c n1 ->
    case b of {
     (,) c0 n2 -> BinNat._N__leb n1 n2}}

insert :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] a1) -> [] a1
insert cmp i l =
  case l of {
   [] -> (:) i [];
   (:) h t ->
    case cmp i h of {
     Prelude.True -> (:) i l;
     Prelude.False -> (:) h (insert cmp i t)}}

insertionsort' :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> ([] a1) -> [] a1
insertionsort' cmp l srtd =
  case l of {
   [] -> srtd;
   (:) h t -> insertionsort' cmp t (insert cmp h srtd)}

insertionsort :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> [] a1
insertionsort cmp l =
  insertionsort' cmp l []

type Coq_election candidate = [] (Coq_ballot candidate)

option_split :: ([] (Prelude.Maybe ((,) a1 a2))) -> (,)
                ([] (Prelude.Maybe a1)) ([] (Prelude.Maybe a2))
option_split l =
  case l of {
   [] -> (,) [] [];
   (:) o t ->
    case o of {
     Prelude.Just p ->
      case p of {
       (,) a b ->
        case option_split t of {
         (,) l1 l2 -> (,) ((:) (Prelude.Just a) l1) ((:) (Prelude.Just b) l2)}};
     Prelude.Nothing ->
      case option_split t of {
       (,) l1 l2 -> (,) ((:) Prelude.Nothing l1) ((:) Prelude.Nothing l2)}}}

tabulate :: (RelDec.RelDec a1) -> (Coq_record a1) -> (Coq_election a1) -> (,)
            ([] ((,) a1 BinNums.N)) (Coq_election a1)
tabulate reldec_candidate rec elect =
  let {get_candidates = List.map (next_ranking reldec_candidate rec) elect}
  in
  case option_split get_candidates of {
   (,) next_ranks next_election ->
    let {counts = tabulate' reldec_candidate next_ranks} in
    let {sorted_ranks = insertionsort cnle counts} in
    (,) sorted_ranks (drop_none next_election)}

gtb_N :: BinNums.N -> BinNums.N -> Prelude.Bool
gtb_N a b =
  Datatypes.negb (BinNat._N__leb a b)

get_bottom_votes :: ([] ((,) a1 BinNums.N)) -> [] a1
get_bottom_votes votes =
  case votes of {
   [] -> [];
   (:) p t ->
    case p of {
     (,) c v ->
      List.map Datatypes.fst
        (List.filter (\x ->
          case x of {
           (,) x0 v' -> BinNat._N__eqb v v'}) votes)}}

find_eliminated' :: (([] a1) -> Prelude.Maybe a1) -> ([] a1) -> ([]
                    ((,) a1 BinNums.N)) -> BinNums.N -> [] a1
find_eliminated' break_tie eliminated0 votes sum =
  case votes of {
   [] -> eliminated0;
   (:) p t ->
    case p of {
     (,) cand count ->
      case t of {
       [] -> eliminated0;
       (:) p0 l ->
        case p0 of {
         (,) cand2 count2 ->
          let {newsum = BinNat._N__add sum count} in
          case BinNat._N__ltb newsum count2 of {
           Prelude.True ->
            find_eliminated' break_tie ((:) cand eliminated0) t sum;
           Prelude.False ->
            case eliminated0 of {
             [] ->
              case break_tie (get_bottom_votes votes) of {
               Prelude.Just l0 -> (:) l0 [];
               Prelude.Nothing -> []};
             (:) c l0 -> eliminated0}}}}}}

find_eliminated :: (([] a1) -> Prelude.Maybe a1) -> ([] ((,) a1 BinNums.N))
                   -> [] a1
find_eliminated break_tie votes =
  find_eliminated' break_tie [] votes BinNums.N0

find_eliminated_noopt :: (([] a1) -> Prelude.Maybe a1) -> ([]
                         ((,) a1 BinNums.N)) -> Prelude.Maybe ([] a1)
find_eliminated_noopt break_tie votes =
  case break_tie (get_bottom_votes votes) of {
   Prelude.Just c -> Prelude.Just ((:) c []);
   Prelude.Nothing -> Prelude.Nothing}

last_item :: ([] ((,) a1 BinNums.N)) -> Prelude.Maybe ((,) a1 BinNums.N)
last_item votes =
  case votes of {
   [] -> Prelude.Nothing;
   (:) h t ->
    case t of {
     [] -> Prelude.Just h;
     (:) y l -> last_item t}}

run_election' :: (RelDec.RelDec a1) -> (([] a1) -> Prelude.Maybe a1) ->
                 (Coq_election a1) -> (Coq_record a1) -> Datatypes.Coq_nat ->
                 (,) ((,) (Prelude.Maybe a1) (Coq_record a1))
                 ([] ([] ((,) a1 BinNums.N)))
run_election' reldec_candidate break_tie elect rec fuel =
  case fuel of {
   Datatypes.O -> (,) ((,) Prelude.Nothing rec) [];
   Datatypes.S n' ->
    case tabulate reldec_candidate rec elect of {
     (,) ranks elect' ->
      let {win_threshhold = BinNat._N__of_nat (Datatypes.length elect')} in
      case last_item ranks of {
       Prelude.Just p ->
        case p of {
         (,) cand1 cand1_votes ->
          case gtb_N
                 (BinNat._N__mul cand1_votes (BinNums.Npos (BinNums.Coq_xO
                   BinNums.Coq_xH))) win_threshhold of {
           Prelude.True -> (,) ((,) (Prelude.Just cand1) rec) ((:) ranks []);
           Prelude.False ->
            case find_eliminated_noopt break_tie ranks of {
             Prelude.Just el ->
              case run_election' reldec_candidate break_tie elect ((:) el
                     rec) n' of {
               (,) p0 t -> (,) p0 ((:) ranks t)};
             Prelude.Nothing -> (,) ((,) Prelude.Nothing rec) []}}};
       Prelude.Nothing -> (,) ((,) Prelude.Nothing rec) []}}}

find_0s :: (RelDec.RelDec a1) -> ([] a1) -> (Coq_election a1) -> [] a1
find_0s reldec_candidate all_candidates el =
  let {get_candidates = List.map (next_ranking reldec_candidate []) el} in
  case option_split get_candidates of {
   (,) next_ranks x ->
    let {initial = List.map (\x0 -> (,) x0 BinNums.N0) all_candidates} in
    let {counts = tabulate'' reldec_candidate next_ranks initial} in
    List.map Datatypes.fst
      (List.filter (\x0 ->
        case x0 of {
         (,) x1 ct -> BinNat._N__eqb ct BinNums.N0}) counts)}

run_election :: (RelDec.RelDec a1) -> (([] a1) -> Prelude.Maybe a1) -> ([]
                (Coq_ballot a1)) -> ([] a1) -> (,)
                ((,) (Prelude.Maybe a1) (Coq_record a1))
                ([] ([] ((,) a1 BinNums.N)))
run_election reldec_candidate break_tie elect all_candidates =
  run_election' reldec_candidate break_tie elect ((:)
    (find_0s reldec_candidate all_candidates elect) [])
    (Datatypes.length elect)

coq_RelDec_eq :: RelDec.RelDec Datatypes.Coq_nat
coq_RelDec_eq =
  EqNat.beq_nat

coq_RelDec_lt :: RelDec.RelDec Datatypes.Coq_nat
coq_RelDec_lt =
  NPeano.ltb

coq_RelDec_le :: RelDec.RelDec Datatypes.Coq_nat
coq_RelDec_le =
  NPeano.leb

coq_RelDec_gt :: RelDec.RelDec Datatypes.Coq_nat
coq_RelDec_gt x y =
  NPeano.ltb y x

coq_RelDec_ge :: RelDec.RelDec Datatypes.Coq_nat
coq_RelDec_ge x y =
  NPeano.leb y x

nat_tabulate :: (Coq_record Datatypes.Coq_nat) -> (Coq_election
                Datatypes.Coq_nat) -> (,)
                ([] ((,) Datatypes.Coq_nat BinNums.N))
                (Coq_election Datatypes.Coq_nat)
nat_tabulate =
  tabulate coq_RelDec_eq

ballot1 :: Coq_ballot Datatypes.Coq_nat
ballot1 =
  (:) ((:) (Datatypes.S (Datatypes.S (Datatypes.S Datatypes.O))) []) ((:)
    ((:) (Datatypes.S (Datatypes.S Datatypes.O)) []) ((:) ((:) (Datatypes.S
    Datatypes.O) []) ((:) ((:) Datatypes.O []) [])))

ballot2 :: Coq_ballot Datatypes.Coq_nat
ballot2 =
  (:) ((:) (Datatypes.S (Datatypes.S Datatypes.O)) []) ((:) ((:) (Datatypes.S
    Datatypes.O) []) ((:) ((:) (Datatypes.S (Datatypes.S (Datatypes.S
    Datatypes.O))) []) ((:) ((:) Datatypes.O []) [])))

ballot3 :: Coq_ballot Datatypes.Coq_nat
ballot3 =
  ballot1

ballot4 :: [] ([] Datatypes.Coq_nat)
ballot4 =
  (:) ((:) Datatypes.O []) ((:) ((:) (Datatypes.S Datatypes.O) []) [])

repeat_append :: ([] a1) -> Datatypes.Coq_nat -> [] a1
repeat_append l n =
  case n of {
   Datatypes.O -> [];
   Datatypes.S n' -> Datatypes.app l (repeat_append l n')}

election1 :: [] (Coq_ballot Datatypes.Coq_nat)
election1 =
  (:) ballot1 ((:) ballot2 ((:) ballot3 ((:) ballot4 [])))

election2 :: [] (Coq_ballot Datatypes.Coq_nat)
election2 =
  repeat_append election1 (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S
    Datatypes.O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

tiebreak :: ([] Datatypes.Coq_nat) -> Prelude.Maybe Datatypes.Coq_nat
tiebreak l =
  case l of {
   [] -> Prelude.Nothing;
   (:) h t -> Prelude.Just h}

