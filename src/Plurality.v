Require Import Coq.Lists.List.
Require Import Classical.
Require Import RelDec.
Require Import Coq.Lists.List.
Require Import Sorting.
Require Import Orders.
Require Import Compare_dec.
Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Require Import Arith.Wf_nat.
Require Import Recdef.
Import ListNotations.


Section election_spec.
  (** For this section, we hold the set of candidates abstract,
      and define ballots and some properties of ballots irrespective
      of how candidates are defined.
   *)
  Variable candidate:Set.
 
  Let ballot := candidate.
  Let election := list ballot.

  Definition participates candidate (election : election) : Prop := 
  In candidate election.

  Inductive voteCount candidate : election -> nat -> Prop :=
  | voteCountCandidate : forall countCandidate election' ct,
      candidate = countCandidate ->
      voteCount candidate election' ct ->
      voteCount candidate (countCandidate :: election') (S ct)
  | voteCountOther : forall countCandidate election' ct,
      candidate <> countCandidate ->
      voteCount candidate election' ct ->
      voteCount candidate (countCandidate :: election') ct
  | voteCountNil : voteCount candidate nil 0.
  

  Definition hasPlurality winningCandidate (election : election) : Prop :=
    forall candidate candidateCount winningCandidateCount,
      candidate <> winningCandidate ->
      voteCount candidate election candidateCount ->
      voteCount winningCandidate election winningCandidateCount ->
      winningCandidateCount > candidateCount.

End election_spec.

Section candidate.

  Local Open Scope N_scope.
  
  Variable candidate : Set.
  Variable reldec_candidate : RelDec (@eq candidate).

  Let ballot := candidate.
  Let election := list ballot.

  Definition getParticipants all :=
    fold_right (fun cand result => if existsb (eq_dec cand) result
                                then result
                                else cand :: result) all all.


  Fixpoint countParticipant election toCount  :=
    fold_right (fun candidate total => if eq_dec toCount candidate then 1 + total else total)
               0 election.

  Definition addTallies participants election :=
    map (fun participant => (participant, countParticipant election participant)) participants.

  Fixpoint getMax' (pairs : list (candidate * N)) (max : (candidate * N * bool)) : option candidate :=
    match pairs, max with
    | (cand, ct) :: t, (maxcd, maxct, _) => if N.eqb ct maxct
                                           then getMax' t (maxcd, maxct, false)
                                           else
                                             if (N.leb ct maxct)
                                             then getMax' t max
                                             else getMax' t (cand, ct, true)
    | [], (maxcd, _, true) => Some maxcd
    | [], (_, _, false) => None
    end.

  Definition getMaxCand pairs : option candidate :=
    match pairs with
    | [] => None
    | h :: t => (getMax' pairs (h, true))
    end.

  Definition runPluralityElection election :=
    let allCandidates := getParticipants election in
    let tally := addTallies allCandidates election in
    getMaxCand tally.

End candidate.

Section cand.

  Variable candidate : Set.
  Variable reldec_candidate : RelDec (@Logic.eq candidate).
  Variable reldec_correct_candidate : RelDec_Correct reldec_candidate.
  
  Local Open Scope N_scope.

  Theorem pluralityCorrect :
    forall election winner,
      runPluralityElection candidate reldec_candidate election = Some winner <->
      hasPlurality candidate winner election.
  Proof.
    intros.
    unfold runPluralityElection.

    Lemma getParticipantsCorrect :
      forall cd election, In cd (getParticipants candidate reldec_candidate election) <->
                     participates candidate cd election.
    Proof.
      split.
      - intros H.
        induction election.
        + auto.
        + simpl in *.
          unfold getParticipants in H.
          simpl in *. destruct (existsb (eq_dec a)
              (fold_right
                 (fun (cand : candidate) (result : list candidate) =>
                  if existsb (eq_dec cand) result then result else cand :: result) 
                 (a :: election) election)) eqn:?.
          * rewrite existsb_exists in *. destruct Heqb.
            intuition. apply reldec_correct_candidate in H2. subst.
            { edestruct (rel_dec_p x cd).
              - auto.
              - right. apply IHelection. unfold getParticipants.
                             
            
  
(*  Fixpoint removeCandidate candidate candidates {struct candidates} :=
    match candidates with
    | h :: t =>
      if eq_dec candidate h then removeCandidate candidate t
      else h :: removeCandidate candidate t
    | [] => []
    end.
  
  Function removeDups all {measure length all} := 
    match all with
    | h :: t => h :: (removeDups (removeCandidate h t))
    | [] => []
    end.
  intros. subst.
  induction t; intros.
  - auto.
  - simpl. destruct (eq_dec h a); auto. simpl in *. 
    Require Coq.omega.Omega. omega.
Defined. *)

  