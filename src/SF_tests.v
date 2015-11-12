Require Import SF_imp.
Require Import RelDec.
Require Import List.
Import ListNotations.


Parameter T : Set.

Parameter eqb_t : T -> T -> bool.

Parameter reldec_t : @RelDec T eq.

Definition option_eq {A} (eq : A -> A -> bool) (a b : option A)  : bool :=
match a,b with
| Some a', Some b' => eq a' b'
| None, None => true
| _, _ => false
end.  

Definition option_eq_t := option_eq eqb_t.

Definition prop_drop_none_keeps (l : list (option T)) (i : T) : bool :=
  Bool.eqb (existsb (option_eq_t (Some i)) l) (existsb (eqb_t i) (drop_none l)).

Definition prop_next_ranking_contains rec bal :=
match (next_ranking T _ rec bal) with
| Some (c, _) => existsb (existsb (eqb_t c)) bal
| _ => true
end.

Definition prop_next_ranking_not_eliminated rec bal :=
match (next_ranking T _ rec bal) with
| Some (c, _) => negb (eliminated T _ rec c)
| _ => true
end.


Fixpoint is_overvote (rec : record T) (b : ballot T) : bool :=
match b with
| [] :: t => is_overvote rec t
| (h :: l) :: t => if (forallb (eq_dec h) l) then 
                     if false (*(eliminated T _ rec h)*) then is_overvote rec t else false
                   else true
| [] => false
end.

Definition prop_next_ranking_not_overvote rec bal :=
match (next_ranking T _ rec bal) with
| Some (c, _) => negb (is_overvote rec bal)
| _ => true
end.

Definition all_props :=
(prop_drop_none_keeps,
prop_next_ranking_contains,
prop_next_ranking_not_eliminated,
prop_next_ranking_not_overvote).
