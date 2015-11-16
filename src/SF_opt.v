Require Import Classical.
Require Import List.
Require Import Arith.

Require Import Ranked_properties.
Require Import SF_spec.
Require Import SF_tactic.
Require Import SF_properties.

(**  The formal specification given in SF_spec always chooses exactly one loser at each
     round; the choice is nondeterministic in the case of ties.  However, the statute
     text and actual election practice is to implement the following optimization:

         In a given round, choose the largest set of losers such that the combined sum
         of continuing votes for all losing candidates is less than the continuing votes
         for all other candidates.  Simultaneously eliminate all losing candidates in this set.

     Here we prove that this procedure is indeed just an optimization of the simple procedure
     that chooses exactly one loser at each round.  Actually, we prove something slightly more
     general, which is that one may chose _any_ set satisfying the condition above and the
     result is unchanged (i.e., prefering the largest such set makes no difference in the end).
  *)

Lemma first_choice_loser_set :
  forall (candidate:Set) e c cs elim x y,
    In c cs ->
    count_votes candidate (fun b => exists c, selected_candidate _ elim b c /\ In c cs) e x ->
    first_choices _ elim c e y ->
    y <= x.
Proof.
  intros candidate e. induction e; simpl; intros.
  * inv H0. inv H1. auto.
  * inv H0; inv H1; auto.
    cut (n' <= n). omega.
    eapply IHe; eauto.
    cut (y <= n). omega.
    eapply IHe; eauto.
    elim H4.
    exists c. split; auto.
    eapply IHe; eauto.
Qed.

Lemma count_votes_total candidates P e :
  exists c, count_votes candidates P e c.
Proof.
  induction e.
  * exists 0. constructor.
  * destruct IHe as [n ?].
    destruct (classic (P a)).
    exists (S n).
    apply count_satisfies; auto.
    exists n.
    apply count_not_satisfies; auto.
Qed.

Lemma count_votes_monotone candidates (P P':ballot candidates -> Prop) e x y :
  (forall b, P b -> P' b) ->
  count_votes candidates P e x ->
  count_votes candidates P' e y ->
  x <= y.
Proof.
  intros. revert x y H0 H1. induction e; intros.
  * inv H0. inv H1. auto.
  * inv H0; inv H1; auto.
    cut ( n <= n0 ). omega.
    apply IHe; auto.
    elim H3. apply H. auto.
Qed.    

Lemma majority_unique :
  forall candidate r e x x',
    SF_spec.majority candidate r e x ->
    SF_spec.majority candidate r e x' ->
    x = x'.
Proof.
  intros.
  destruct (classic (x = x')); auto. elimtype False.
  destruct (SF_spec.total_selected_total candidate r e) as [t ?].
  destruct (SF_spec.sf_first_choices_total candidate r e x) as [n ?].
  destruct (SF_spec.sf_first_choices_total candidate r e x') as [n' ?].
  generalize (H t n H2 H3); intro.
  generalize (H0 t n' H2 H4); intro.
  assert ( n + n' <= t ).
  { clear H H0 H5 H6.
    revert t n n' H2 H3 H4.
    induction e; simpl; intros.
    inv H2. inv H3. inv H4. auto.
    inv H2. inv H3. inv H4.
    elim H1.
    eapply selected_candidate_unique; eauto.
    cut (n'0 + n' <= n0). omega.
    apply IHe; eauto.
    inv H4.
    cut (n + n'0 <= n0). omega.
    apply IHe; eauto.
    cut (n + n' <= n0). omega.
    apply IHe; eauto.
    inv H3.
    rewrite exhausted_ballot_next_ranking_iff in H5.
    destruct H2.
    destruct H0 as [q [??]].
    elim H.
    right. exists q. split; auto.
    inv H4.
    rewrite exhausted_ballot_next_ranking_iff in H5.
    destruct H3.
    destruct H0 as [q [??]].
    elim H.
    right. exists q. split; auto.
    apply IHe; auto.
  }
  omega.
Qed.


Lemma winner_elim_eq :
  forall candidate elim elim' e c,
    (forall x, elim x <-> elim' x) ->
    SF_spec.winner candidate e elim c ->
    SF_spec.winner candidate e elim' c.
Admitted.

Lemma exausted_ballot_monotone :
  forall (candidate:Set) (elim elim':candidate -> Prop) b,
    (forall x, elim x -> elim' x) ->
    SF_spec.exhausted_ballot candidate elim b ->
    SF_spec.exhausted_ballot candidate elim' b.
Proof.
  unfold exhausted_ballot. firstorder.
  left. intros [r ?].
  induction H1.
  destruct (classic (Forall elim r')).
  apply IHnext_ranking.
  intros.
  apply (H0 x).
  apply SF_spec.next_ranking_eliminated; auto.
  apply (H0 r').
  destruct r'.
  elim H4.
  rewrite Forall_forall.
  simpl; intuition.
  apply SF_spec.next_ranking_valid with c; simpl; auto.
  right.
  intro.
  apply H4.
  rewrite Forall_forall; intros.
  destruct (classic (x = c)).
  subst x; auto.
  elim H2.
  exists x. exists c.
  simpl; intuition.
  apply (H0 r).
  apply SF_spec.next_ranking_valid with c; auto.
  intuition.
  right. exists x. split; auto.
  induction H0.
  apply SF_spec.next_ranking_eliminated; auto.
  rewrite Forall_forall. intros.
  apply H.
  rewrite Forall_forall in H0; auto.
  apply SF_spec.next_ranking_valid with c; auto.
  intuition.
  left.
  red; eauto.
  red; eauto.
Qed.

Section sf_spec_opt.
  Variable candidate : Set.
  Variable e : election candidate.
  Variable losers : list candidate.
  Variable loserCount : nat.

  Variables eliminated eliminated':candidate -> Prop.
  
  Hypothesis Hdups : NoDup losers.

  Hypothesis Hcount : count_votes _ (fun b => exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers) e loserCount.
  Hypothesis Hviable : forall l, In l losers -> viable_candidate _ eliminated e l.
  Hypothesis Hdominated :
      forall c count,
         ~In c losers ->
         SF_spec.viable_candidate _ eliminated e c ->
         SF_spec.first_choices _ eliminated c e count ->
         loserCount < count.
  Hypothesis Helim_eq :
      forall x, eliminated' x <-> eliminated x \/ In x losers.

  Lemma sf_opt_loser_in_set : 
    forall
      (loser : candidate),
      length losers > 0 ->
      is_loser candidate eliminated e loser ->
      In loser losers.
  Proof.
    intros.
    destruct (classic (In loser losers)); auto. elimtype False.
    destruct (SF_spec.sf_first_choices_total _ eliminated e loser) as [lCount HlCount].
    assert (loserCount < lCount).
    apply Hdominated with loser; auto.
    destruct H0; auto.
    destruct losers.
    simpl in H. omega.
    destruct H0.
    destruct (SF_spec.sf_first_choices_total _ eliminated e c) as [cn Hcn].
    assert( lCount <= loserCount ).
    transitivity cn.
    apply H3 with c; auto.
    apply Hviable. simpl; auto.
    eapply first_choice_loser_set; eauto. simpl; auto.
    simpl in H2.
    omega.
  Qed.

  Lemma sf_opt_inductive_step :
    forall
      (loser : candidate)
      (losers' : list candidate),

      is_loser candidate eliminated e loser ->
      (forall x0 : candidate, In x0 losers <-> x0 = loser \/ In x0 losers') ->

      forall (c : candidate) (count : nat),
        ~ In c losers' ->
        viable_candidate candidate (update_eliminated candidate eliminated loser) e c ->
        first_choices candidate (update_eliminated candidate eliminated loser) c e count ->
        loserCount < count.
   Proof.
     intros.
     destruct (SF_spec.sf_first_choices_total _ eliminated e c) as [count0 ?].
     destruct (SF_spec.sf_first_choices_total _ eliminated e loser) as [lCount HlCount].
     assert ( count0 > 0 \/ (lCount = 0 /\ count0 = 0) ).
     { destruct count0. auto.
       cut ( lCount <= 0 ). omega.
       destruct H.
       apply H5 with c; auto.
       destruct H2; split; auto.
       intro. apply H2; hnf; auto.
       left. omega.
     }
     destruct H5.
     apply lt_le_trans with count0; auto.
     apply (Hdominated c count0); auto.
     intro.
     rewrite H0 in H6.
     destruct H6; auto.
     { subst c. destruct H2. elim H2; hnf; auto. }
     { destruct H2; split; auto.
       intro. apply H2; hnf; auto. }
     apply first_choices_monotone with candidate eliminated (SF_spec.update_eliminated _ eliminated loser) e c; auto.
     unfold update_eliminated; simpl; auto.        
     { intros [?|?].
       destruct H2.
       elim H2; hnf; simpl; auto.
       subst c.
       destruct H2. elim H2; hnf; auto.
     }
     unfold update_eliminated; simpl; auto.        
     destruct H5. subst.
     destruct (classic (In c losers)).
     rewrite H0 in H5.
     destruct H5. 2: elim H1; auto.
     subst c.
     destruct H2.
     elim H2; hnf; simpl; auto.
     assert (loserCount < 0).
     apply Hdominated with c; auto.
     destruct H2; split; auto.   
     intro; apply H2; hnf; auto.
     elimtype False; omega.
   Qed.

   Lemma sf_opt_majority_forward :
     forall w,
       majority _ eliminated e w ->
       majority _ eliminated' e w.
   Proof.
     repeat intro.
     destruct (SF_spec.sf_first_choices_total _ eliminated e w) as [wc ?].
     destruct (SF_spec.total_selected_total _ eliminated e) as [t ?].
     generalize (H t wc H3 H2). intros.
     red. red in H4.
     assert ( wc <= winner_votes ).
     { eapply first_choices_monotone.
       2: apply H2.
       2: apply H1.
       rewrite Helim_eq. intros [?|?].
admit. (* majority candidate is not eliminated... *)
admit. (* FIXME. need to know that there is a viable candidate not in
          the losers set *)
       intros.
       rewrite Helim_eq. auto.
     }
     assert ( total_votes <= t ).
     { clear -H0 H3 Helim_eq.
       revert total_votes t H0 H3.
       induction e; intros.
       inv H3. inv H0. auto.
       inv H3. inv H0.
       cut (n0 <= n). omega.
       apply IHe0; auto.
       transitivity n.
       apply IHe0; auto.
       omega.
       inv H0.
       elim H3.
       eapply exausted_ballot_monotone.
       2: eauto.
       intros. rewrite Helim_eq. auto.
       apply IHe0; auto.
     }
     omega.
  Qed.

End sf_spec_opt.


Lemma next_ranking_back :
  forall (candidate:Set) (elim elim':candidate -> Prop) b r c,
    (forall x, elim x -> elim' x) ->
    In c r ->
    next_ranking _ elim' b r ->
    next_ranking _ elim b r \/
    (exists c' r',
       ~overvote _ r' /\
       next_ranking _ elim b r' /\
       In c' r' /\ elim' c' /\ ~elim c').
Proof.
  intros. induction H1.
  * destruct (classic (Forall elim r')).
    destruct IHnext_ranking; auto.
    left. apply SF_spec.next_ranking_eliminated; auto.
    destruct H5 as [c' [q [?[?[?[??]]]]]].
    right.
    exists c'. exists q. intuition.
    apply SF_spec.next_ranking_eliminated; auto.    
    destruct (classic (exists x, In x r' /\ ~elim x)).
    destruct H5 as [x [??]].
    right. exists x. exists r'.
    repeat split; auto.
    apply SF_spec.next_ranking_valid with x; auto.
    rewrite Forall_forall in H1.
    apply H1; auto.
    elim H4.
    rewrite Forall_forall; intros.
    destruct (classic (elim x)); auto.
    elim H5.
    eauto.
  * left. apply SF_spec.next_ranking_valid with c0; auto.
    intuition.
Qed.

Lemma continuing_ballot_back :
  forall (candidate:Set) (elim elim':candidate -> Prop) b,
  (forall x, elim x -> elim' x) ->
  continuing_ballot _ elim' b ->
  continuing_ballot _ elim b.
Proof.
  repeat intro.
  apply H0.
  destruct H1.
  left. intros [r ?]. elim H1.
  clear H0 H1.
  induction H2.
  destruct (classic (exists x, In x r' /\ ~elim x)).
  destruct H3 as [x [??]].
  exists r'.
  apply SF_spec.next_ranking_valid with x; auto.
  destruct IHnext_ranking as [q ?].
  exists q.
  apply SF_spec.next_ranking_eliminated; auto.
  rewrite Forall_forall; intros.
  destruct (classic (elim x)); auto.
  elim H3; eauto.
  exists r.
  apply SF_spec.next_ranking_valid with c; auto.
  intuition.
  destruct H1 as [r [??]].
  clear H0.
  hnf.
  right.
  exists r. split; auto.
  induction H1.
  apply SF_spec.next_ranking_eliminated; auto.
  rewrite Forall_forall; intros.
  apply H.
  rewrite Forall_forall in H0.
  apply H0; auto.
  apply SF_spec.next_ranking_valid with c; auto.
Qed.


Lemma selected_candidate_back :
  forall (candidate:Set) (elim elim':candidate -> Prop) b c,
    (forall x, elim x -> elim' x) ->
    selected_candidate _ elim' b c ->
    selected_candidate _ elim b c \/
    (exists x, selected_candidate _ elim b x /\ elim' x /\ ~elim x).
Proof.
  intros.
  destruct H0.
  destruct H1 as [r [??]].
  destruct (next_ranking_back candidate elim elim' b r c); auto.
  left. split; auto.
  eapply continuing_ballot_back; eauto.
  eauto.
  destruct H3 as [c' [r' [?[?[?[??]]]]]].
  right. exists c'.
  repeat split; auto.
  eapply continuing_ballot_back; eauto.
  exists r'; split; auto.
Qed.

Lemma count_votes_unique :
  forall (candidate:Set) (P:ballot candidate -> Prop) e n1 n2,
    count_votes _ P e n1 ->
    count_votes _ P e n2 ->
    n1 = n2.
Proof.
  intros until e. induction e; intros.
  * inv H. inv H0. auto.
  * inv H; inv H0; auto.
    elim H2; auto.
    elim H3; auto.
Qed.

Lemma count_votes_add :
  forall (candidate:Set) (P1 P2 P:ballot candidate -> Prop) e n1 n2,
    (forall b, P b <-> P1 b \/ P2 b) ->
    (forall b, P1 b -> P2 b -> False) ->
    count_votes _ P1 e n1 ->
    count_votes _ P2 e n2 ->
    count_votes _ P e (n1+n2).
Proof.
  intros. revert n1 n2 H1 H2.
  induction e; intros.
  * inv H1. inv H2. simpl. constructor.
  * inv H1; inv H2.
    elim (H0 a); auto.
    simpl.
    apply count_satisfies.
    apply H. auto.
    apply IHe; auto.
    replace (n1 + S n) with (S (n1 + n)) by omega.
    apply count_satisfies.
    apply H; auto.
    apply IHe; auto.
    apply count_not_satisfies.
    intro.
    rewrite H in H1.
    intuition.
    apply IHe; auto.
Qed.

Lemma elim_loser_list :
  forall
    (candidate:Set)
    (eliminated:candidate -> Prop)
    (losers : list candidate)
    (losers' : list candidate)
    (loser  : candidate)
    b,
    
    (In loser losers) ->
    (forall x, In x losers <-> x = loser \/ In x losers') ->
    (exists c, SF_spec.selected_candidate _ (update_eliminated _ eliminated loser) b c /\ In c losers') ->
    (exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers).
Proof.
  intros.
  destruct H1 as [c [??]].
  destruct (selected_candidate_back _ eliminated (update_eliminated _ eliminated loser) b c); auto.
  { unfold update_eliminated; auto. }
  exists c; split; auto.
  rewrite H0; auto.
  destruct H3 as [x [?[??]]].
  hnf in H4.
  destruct H4. contradiction.
  subst x.
  exists loser; auto.
Qed.  

Lemma decompose_losers' :
 forall
    (candidate:Set)
    (eliminated:candidate -> Prop)
    (e:election candidate)
    (losers : list candidate)
    (loser  : candidate),
   NoDup losers ->
   In loser losers ->
   (forall l, In l losers -> viable_candidate _ eliminated e l) ->

   exists losers',
     NoDup losers' /\
     (forall l, In l losers' -> viable_candidate _ (update_eliminated _ eliminated loser) e l) /\
     length losers = S (length losers') /\
     (~In loser losers') /\
     (forall x, In x losers <-> x = loser \/ In x losers').
Proof.
  intros until losers. induction losers; intros. elim H0.
  inv H.
  simpl in H0. destruct H0.
  * subst a.
    exists losers.
    intuition.
    destruct (H1 loser); simpl; auto.
    split; auto.
    unfold update_eliminated.
    intuition.
    destruct (H1 l); simpl; auto.
    subst l; auto.
    destruct (H1 l); simpl; auto.
    simpl in H. intuition.
    simpl; auto.
  * destruct (IHlosers loser) as [losers' [?[?[?[??]]]]]; auto.
    intros; apply H1; simpl; auto.
    exists (a::losers'); intuition.
    constructor; auto.
    intro.
    apply H4.
    rewrite H7. auto.
    simpl in H8. destruct H8.
    subst l.
    destruct (H1 a); simpl; auto.
    split; auto.
    unfold update_eliminated; auto.
    intuition.
    subst a. contradiction.
    destruct (H1 l); simpl; auto.
    rewrite H7; auto.
    simpl. omega.
    simpl in H8.
    destruct H8.
    subst a.
    contradiction.
    contradiction.
    simpl in H8.
    rewrite H7 in H8.
    simpl. intuition.
    simpl; auto.
    subst x; auto.
    simpl in H9; simpl.
    rewrite H7.
    intuition.
Qed.


Lemma decompose_losers :
 forall
    (candidate:Set)
    (eliminated:candidate -> Prop)
    (e:election candidate)
    (losers : list candidate)
    (loser  : candidate)
    (loserCount : nat),
   NoDup losers ->
   In loser losers ->
   count_votes _ (fun b => exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers) e loserCount ->
   (forall l, In l losers -> viable_candidate _ eliminated e l) ->

   exists losers' loserCount',
     NoDup losers' /\
     count_votes _ (fun b => exists c, SF_spec.selected_candidate _ (update_eliminated _ eliminated loser) b c /\ In c losers') e loserCount' /\
     (forall l, In l losers' -> viable_candidate _ (update_eliminated _ eliminated loser) e l) /\
     loserCount' <= loserCount /\
     length losers = S (length losers') /\
     (~In loser losers') /\
     (forall x, In x losers <-> x = loser \/ In x losers').
Proof.
  intros.
  destruct (decompose_losers' candidate eliminated e losers loser)
           as [losers' [?[?[?[??]]]]]; auto.
  destruct (count_votes_total _
        (fun b : list (list candidate) =>
        exists c : candidate,
          selected_candidate candidate
            (update_eliminated candidate eliminated loser) b c /\ 
          In c losers') e) as [loserCount' ?].
  exists losers', loserCount'.
  intuition.
  eapply count_votes_monotone.
  2: eauto. 2: eauto.
  simpl.
  intro b.
  apply elim_loser_list; auto.
Qed.



Theorem sf_spec_optimization_backward :
  forall (candidate:Set)
         (len : nat)
         (eliminated eliminated':candidate -> Prop)
         (e:election candidate)
         (losers:list candidate)
         (loserCount:nat),
    
      len = length losers ->
      NoDup losers ->
      (forall l, In l losers -> viable_candidate _ eliminated e l) ->
      count_votes _ (fun b =>
                       exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers)
                  e loserCount ->
      (forall c count,
         ~In c losers ->
         SF_spec.viable_candidate _ eliminated e c ->
         SF_spec.first_choices _ eliminated c e count ->
         loserCount < count) ->
      (forall x, eliminated' x <-> eliminated x \/ In x losers) ->
      (forall x, 
         SF_spec.winner candidate e eliminated' x ->
         SF_spec.winner candidate e eliminated x).
Proof.
  intros candidate n.
  induction n.
  * intros. 
    eapply winner_elim_eq. 2: eauto.
    intro.
    rewrite H4.
    intuition.
    destruct losers. elim H7.
    inv H.
  * intros.
    destruct (classic (exists winner, majority _ eliminated e winner)).
    + destruct H6 as [winner ?].
      apply SF_spec.winner_now.
      replace x with winner; auto.
      inv H5.
      symmetry.
      eapply majority_unique.
      apply H7.
      eapply sf_opt_majority_forward; eauto.
      elim H7.
      exists winner.
      eapply sf_opt_majority_forward; eauto.
    + assert (exists loser, In loser losers /\ is_loser _ eliminated e loser).
      { destruct (sf_loser_exists _ e eliminated) as [loser ?].
        destruct losers. inversion H.
        exists c; auto.
        destruct (H1 c); simpl; auto.
        exists loser; split; auto.
        eapply sf_opt_loser_in_set; eauto.
        rewrite <- H. omega.
      }
      destruct H7 as [loser [??]].
      apply SF_spec.winner_elimination with loser; auto.
      destruct (decompose_losers _ eliminated e losers loser loserCount) as [losers' [loserCount' [?[?[?[?[?[??]]]]]]]]; auto.
      apply (IHn _ eliminated' e losers' loserCount'); auto.
      omega.
      eapply sf_opt_inductive_step; eauto.
      intros.
      apply le_lt_trans with loserCount; eauto.
      unfold update_eliminated.
      intro.
      rewrite H4.
      rewrite H15.
      intuition.
Qed.

Theorem sf_spec_optimization_forward :
  forall (candidate:Set)
         (len : nat)
         (eliminated eliminated':candidate -> Prop)
         (e:election candidate)
         (losers:list candidate)
         (loserCount:nat),
    
      len = length losers ->
      NoDup losers ->
      (forall l, In l losers -> viable_candidate _ eliminated e l) ->
      count_votes _ (fun b =>
                       exists c, SF_spec.selected_candidate _ eliminated b c /\ In c losers)
                  e loserCount ->
      (forall c count,
         ~In c losers ->
         SF_spec.viable_candidate _ eliminated e c ->
         SF_spec.first_choices _ eliminated c e count ->
         loserCount < count) ->
      (forall x, eliminated' x <-> eliminated x \/ In x losers) ->
      (forall x, 
         SF_spec.winner candidate e eliminated x ->
         SF_spec.winner candidate e eliminated' x).
Proof.
  intros candidate n.
  induction n.
  * intros.
    eapply winner_elim_eq. 2: eauto.
    intro.
    rewrite H4.
    intuition.
    destruct losers. elim H7.
    inv H.
  * intros.
    inv H5.
      - apply SF_spec.winner_now.
        eapply sf_opt_majority_forward; eauto.
      - assert (In loser losers).
        { eapply sf_opt_loser_in_set; eauto.
          rewrite <- H. omega.
        }
        destruct (decompose_losers _ eliminated e losers loser loserCount) as [losers' [loserCounts' [?[?[?[?[?[??]]]]]]]]; auto.
        apply (IHn (SF_spec.update_eliminated _ eliminated loser) eliminated' e losers' loserCounts'); auto.
        rewrite H13 in H.
        injection H; auto.
        eapply sf_opt_inductive_step; eauto.
        intros.
        apply le_lt_trans with loserCount; eauto.
        unfold update_eliminated.
        intro.
        rewrite H4.
        rewrite H15.
        intuition.
Qed.
