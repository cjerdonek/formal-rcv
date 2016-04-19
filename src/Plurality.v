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

  Inductive voteCount candidate : election -> N -> Prop :=
  | voteCountCandidate : forall countCandidate election' ct,
      candidate = countCandidate ->
      voteCount candidate election' ct ->
      voteCount candidate (countCandidate :: election') (ct + 1)
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
      N.gt winningCandidateCount candidateCount.

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
                                else cand :: result) nil all.
  
  Definition countParticipant election toCount  :=
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

  Lemma existb_false_forall : forall A l b, (@existsb A b l = false) <-> (forall i, In i l -> b i = false).
    intros A l b; split.
    - induction l.
      + simpl. intuition.
      + simpl. intros. 
        rewrite Bool.orb_false_iff in *.
        intuition; subst; auto.
    - induction l.
      + simpl. intuition.
      + intuition. simpl. rewrite Bool.orb_false_iff. intuition.
  Qed.
  
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
                 [] election)) eqn:?.
        * rewrite existsb_exists in *. destruct Heqb.
          intuition.
        * rewrite existb_false_forall in Heqb.
          { edestruct (rel_dec_p a cd).
            - auto.
            - right.
              apply IHelection. unfold getParticipants. inversion H. intuition. auto.
          }
    - intros.
      induction election.
      + auto.
      + simpl. destruct (existsb (eq_dec a) (getParticipants candidate reldec_candidate election)) eqn:?.
        rewrite existsb_exists in Heqb. destruct Heqb. intuition. apply reldec_correct_candidate in H2. subst.
        inversion H; subst; clear H; auto. simpl.
        destruct (rel_dec_p a cd). auto. inversion H; auto.
  Qed.

  Lemma fold_right_cons : forall B A (f:B -> A -> A) (l:list B) b a0, fold_right f a0 (b::l) = f b (fold_right f a0 l).
  Proof.
    intros; reflexivity.
  Defined.
  
  
  Theorem count_correct : forall election cand count,
      countParticipant candidate reldec_candidate election cand = count <-> voteCount candidate cand election count.
  Proof.
    intros election. split. revert count.
    - induction election; intros.
      + simpl in H. subst. constructor.
      + unfold countParticipant in H. rewrite fold_right_cons in H.
        destruct (eq_dec cand a) eqn:?.
        * subst. rewrite N.add_comm.
          { constructor.
            - apply reldec_correct_candidate in Heqb. auto.
            - apply IHelection. unfold countParticipant. auto.
          }
        * apply neg_rel_dec_correct in Heqb.
          { constructor.
            - auto.
            - apply IHelection. subst. auto.
          }
    - intros. generalize dependent count. induction election; intros.
      + simpl. inversion H. auto.
      + unfold countParticipant. rewrite fold_right_cons.
        destruct (eq_dec cand a) eqn:?.
        * apply reldec_correct_candidate in Heqb.
          subst.
          { inversion H.
            - subst. rewrite (N.add_comm ct). f_equal.
              apply IHelection. auto.
            - intuition.
          }
        * apply neg_rel_dec_correct in Heqb.
          inversion H; intuition.
  Qed.

  Theorem getMax'_correct : forall (prs : list (candidate * N)) maxcand maxct unique totalMax,
      getMax' candidate prs (maxcand, maxct, unique) = Some totalMax ->
      (exists totalMaxCt, (In (totalMax, totalMaxCt) prs \/ (totalMaxCt = maxct /\ totalMax = maxcand)) /\
                     (forall ct, In ct (map (@snd candidate _) (prs : list (candidate * N))) -> totalMaxCt > ct)).
    intros prs.
    induction prs; intros.
    - simpl in *. destruct unique eqn:?. subst. inversion H.
      subst. eexists. split. eauto. intuition. congruence.
    - simpl in H. destruct a. simpl. destruct (n =? maxct) eqn:?.
      + apply IHprs in H. destruct H. intuition.
        *  exists x. intuition. apply H1. subst. apply N.eqb_eq in Heqb. subst.
           
        apply IHprs.
  
  Theorem getMaxCand_correct : forall cand prs election mx,
      (forall cnd cnt, In (cnd, cnt) prs -> voteCount candidate cnd election cnt) ->
      (getMax' candidate mx = Some cand <-> hasPlurality candidate cand election).
  Proof.
    intros cand prs election H.
    split; intros.
    - induction prs.
      + simpl in *; congruence.
      + simpl in H0. 
    
       
                               
  
  
  Theorem pluralityCorrect :
    forall election winner,
      runPluralityElection candidate reldec_candidate election = Some winner <->
      hasPlurality candidate winner election.
  Proof.
    intros.
    unfold runPluralityElection. split. intros.
    unfold hasPlurality. intros candidate0 candidateCount winningCandidateCount H0 H1 H2.
    
    

            
  
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
Defined. 