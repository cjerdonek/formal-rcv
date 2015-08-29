Require sf_imp.
Require sf_spec.
Require Import RelDec.
Require Import List.
Require Import Sorted.
Require Import Permutation.
Import ListNotations.


Section cand.

Variable candidate : Set.
Variable reldec_candidate : RelDec (@eq candidate).
Variable reldec_correct_candidate : RelDec_Correct reldec_candidate.

Definition in_record (rec : sf_imp.record candidate) (c : candidate) :=
exists e, In e rec /\ In c e.

Lemma no_viable_candidates_correct : 
forall rec bal,
sf_imp.no_viable_candidates candidate _ rec bal = true -> 
sf_spec.no_viable_candidates candidate (in_record rec) bal.
Proof.
intros.
unfold sf_imp.no_viable_candidates in *. rewrite forallb_forall in H.
unfold sf_spec.no_viable_candidates.
intros.
specialize (H _ H0). unfold sf_imp.no_viable_candidates_selection in *.
rewrite forallb_forall in H. apply H in H1.
unfold sf_imp.eliminated in H1.
rewrite existsb_exists in H1.
destruct H1.
unfold in_record. destruct H1.
rewrite existsb_exists in H2. destruct H2.
destruct H2. 
apply reldec_correct_candidate in H3. subst.
exists x. auto.
Qed.

Lemma existsb_false_forall :
forall A (b: A -> bool) l,
existsb b l = false ->
forallb (fun x => (negb (b x))) l = true.
Proof.
intros. rewrite forallb_forall. intros.
induction l.
- simpl in H. inversion H0.
- simpl in *. rewrite Bool.orb_false_iff in H.
  destruct H. 
  destruct H0.
  + subst. rewrite H. auto.
  + intuition.
Qed.

Lemma eliminated_correct :
forall rec can,
sf_imp.eliminated candidate _ rec can = true <->
in_record rec can.
Proof.
split.
intros.
unfold sf_imp.eliminated in *. rewrite existsb_exists in H.
destruct H; intuition.
rewrite existsb_exists in H1. destruct H1; intuition.
unfold in_record.
apply reldec_correct_candidate in H2. subst; eauto.
intros.
unfold sf_imp.eliminated in *. rewrite existsb_exists.
unfold in_record in H. destruct H. exists x. intuition.
rewrite existsb_exists. exists can. intuition.
apply reldec_correct_candidate. auto.
Qed.

Definition no_viable_candidates eliminated (b : sf_spec.ballot candidate) :=
Forall (Forall eliminated) b.

Lemma no_viable_candidates_Forall :
forall eliminated b,
no_viable_candidates eliminated b <->
sf_spec.no_viable_candidates candidate eliminated b.
Proof.
intros.
unfold no_viable_candidates.
unfold sf_spec.no_viable_candidates.
intuition. rewrite Forall_forall in *.
specialize (H rank). rewrite Forall_forall in H. 
intuition.
rewrite Forall_forall. intro. rewrite Forall_forall. intuition.
specialize (H x). intuition.
Qed.

Lemma next_ranking_correct :
forall rec bal cd bal' ,
sf_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
exists l,(sf_spec.next_ranking candidate (in_record rec) bal l /\ Forall (eq cd) l).
Proof.
intros.
induction bal.
- simpl in *. congruence.
- simpl in *.
  destruct a.
  + intuition. destruct H0. exists x. firstorder.
  + destruct (forallb (eq_dec c) a) eqn:Heqb0.
    * { destruct (sf_imp.eliminated candidate reldec_candidate rec c) eqn:?.
         - apply IHbal in H. clear IHbal.
           destruct H. destruct H. exists x.
           split. left. intuition.
           + intros.
             assert (c = c0).
             destruct H1. auto.
             rewrite forallb_forall in Heqb0.
             apply Heqb0 in H1.
             apply reldec_correct_candidate in H1. auto.
             subst.
             unfold sf_imp.eliminated in Heqb. rewrite existsb_exists in Heqb.
             destruct Heqb. intuition. rewrite existsb_exists in *. destruct H4.
             destruct H2. apply reldec_correct_candidate in H4. subst.
             unfold in_record. eauto.               
           + intuition.
         - inversion H. subst. clear H. 
           exists (cd :: a).
           split. right.
           split.
           + unfold sf_imp.eliminated in *. 
             apply existsb_false_forall in Heqb.
             rewrite forallb_forall in Heqb.
             exists cd.
             split.
             * constructor. auto.
             * intro. unfold in_record in *.
               destruct H. destruct H. specialize (Heqb x H).
               rewrite Bool.negb_true_iff in Heqb.
               apply existsb_false_forall in Heqb.
               rewrite forallb_forall in Heqb.
               specialize (Heqb cd). intuition.
               rewrite Bool.negb_true_iff in H1.
               assert (cd = cd) by reflexivity.
               apply reldec_correct_candidate in H2.
               unfold eq_dec in *.
               congruence.
           + reflexivity.
           + rewrite forallb_forall in Heqb0. rewrite Forall_forall. 
             intuition. destruct H. auto. apply Heqb0 in H. apply reldec_correct_candidate.
             auto.                                                                     
      } 
    * congruence.       
Qed.


Lemma next_ranking_in :
forall e bal x,
  sf_spec.next_ranking candidate e bal x ->
  In x bal.
Proof.
induction bal; intros.
- simpl in H. auto.
- simpl in *. intuition.
Qed.

Lemma next_ranking_cons_or :
forall b1 bal e x,
sf_spec.next_ranking candidate e (b1 :: bal) x ->
sf_spec.next_ranking candidate e [b1] x \/ 
sf_spec.next_ranking candidate e bal x.
intros. simpl in  H. intuition. destruct H. destruct H.
left. unfold sf_spec.next_ranking. right. eauto.
Qed.

Ltac inv H := inversion H; subst; clear H.

Lemma overvote_cons_or :
forall b1 bal e ,
sf_spec.overvote candidate e (b1 :: bal) ->
sf_spec.overvote candidate e [b1] \/ sf_spec.overvote candidate e bal.
Proof.
intros.
inv H.  
intuition.
destruct H1. destruct H0.
intuition.
edestruct (next_ranking_cons_or); eauto.
- unfold sf_spec.overvote.
  left. exists x. split; eauto.
- right. unfold sf_spec.overvote. exists x; split; eauto.
Qed.

Lemma next_ranking_not_overvote :
forall rec bal cd bal',
sf_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
~sf_spec.overvote candidate (in_record rec) bal.
Proof.
intros.
induction bal.
- simpl in *. congruence.
- simpl in *.
  destruct a.
  + intro.
    unfold sf_spec.overvote in H0.
    destruct H0.
    destruct H0.
    simpl in H0.
    intuition. 
    unfold sf_spec.overvote in H2. apply H2. eauto.
    subst. destruct H1. destruct H1. intuition.
  + destruct (forallb (eq_dec c) a) eqn:?.
    * { destruct (sf_imp.eliminated candidate reldec_candidate rec c) eqn:?.
        - intuition. 
          edestruct (overvote_cons_or); eauto.
          + rewrite forallb_forall in *. 
            clear -H2 Heqb reldec_correct_candidate.
            inversion H2. intuition.
            inversion H0. intuition.
            intuition. subst. intuition.
            destruct H1. destruct H.
            intuition. apply H5.
            simpl in *. intuition; subst; auto. 
            * specialize (Heqb x0). intuition.
              apply reldec_correct_candidate in H. auto.
            * specialize (Heqb x). intuition.
              apply reldec_correct_candidate in H. auto.
            * assert (x = c).
              specialize (Heqb x). intuition. apply reldec_correct_candidate in H.
              auto.
              assert (x0 = c).               
              specialize (Heqb x0). intuition. apply reldec_correct_candidate in H7.
              auto.
              subst. auto.
        - inv H. intro.
          inv H. clear IHbal.
          intuition.
          destruct H1. destruct H0. intuition. inv H.
          destruct H2. specialize (H cd). simpl in H. intuition.
          rewrite <- eliminated_correct in H. congruence.
          intuition. subst.
          apply H3.
          rewrite forallb_forall in Heqb. 
          simpl in *. intuition; subst; auto.
          + specialize (Heqb _ H1). apply reldec_correct_candidate in Heqb. 
            auto.
          + specialize (Heqb _ H2). apply reldec_correct_candidate in Heqb.
            auto.
          + assert (x0 = cd); subst. 
            specialize (Heqb _ H2). apply reldec_correct_candidate in Heqb. auto.
            assert (x1 = cd); subst.
            specialize (Heqb _ H1). apply reldec_correct_candidate in Heqb. auto.
            auto. } 
    * congruence.
Qed.
    
Lemma no_viable_candidates_cons :
forall a b e,
sf_spec.no_viable_candidates candidate (e) (a ::  b) <->
(sf_spec.no_viable_candidates candidate e [a] /\
sf_spec.no_viable_candidates candidate e b).
split.
intros.
unfold sf_spec.no_viable_candidates in *.
split.
intros. eapply H; eauto. inv H0; simpl in *; intuition.
intros. eapply H; eauto. simpl. intuition.
intros. intuition.
unfold sf_spec.no_viable_candidates in *. simpl in *.
intuition. eapply H0; eauto. 
eapply H1; eauto.
Qed.

Lemma next_ranking_viable :
forall bal rec cd bal',
sf_imp.next_ranking candidate reldec_candidate rec bal =
      Some (cd, bal') ->
~sf_spec.no_viable_candidates candidate (in_record rec) bal.
Proof.
induction bal; intros.
- simpl in *. congruence.
- simpl in *. destruct a.
  + intro. apply no_viable_candidates_cons in H0. destruct H0.
    eapply IHbal in H1; eauto.
  + destruct (forallb (eq_dec c) a).
    * { destruct (sf_imp.eliminated candidate reldec_candidate rec c) eqn:?.
        - apply eliminated_correct in Heqb.
          intro. apply no_viable_candidates_cons in H0.
          destruct H0.
          eapply IHbal in H1; eauto.
        - inv H. intro. apply no_viable_candidates_cons in H. destruct H.
          unfold sf_spec.no_viable_candidates in H. 
          specialize (H (cd :: a)). simpl in H. intuition. clear H2.
          specialize (H cd). intuition. clear H2. 
          rewrite <- eliminated_correct in H. congruence.
      }
    * congruence.
Qed.
  

Lemma next_ranking_selected :
forall bal cd bal' rec,
sf_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
sf_spec.selected_candidate candidate (in_record rec) bal cd.
split.
intros.
unfold sf_spec.selected_candidate. 
- unfold sf_spec.continuing_ballot. intro. 
  unfold sf_spec.exhausted_ballot in H0.
  destruct H0. 
  + apply next_ranking_viable in H. auto.
  + eapply next_ranking_not_overvote in H0; eauto.
- apply next_ranking_correct in H. destruct H. destruct H.
  exists x. intuition.
  destruct x. induction bal. inv H. simpl in *. intuition. subst. 
  destruct H; intuition.
  inv H0. simpl in *. auto.
Qed.

Lemma next_ranking_eliminated :
forall bal rec,
sf_imp.next_ranking candidate _ rec bal = None ->
sf_spec.exhausted_ballot candidate (in_record rec) bal.
Proof.
intros.
unfold sf_spec.exhausted_ballot.
induction bal.
-  left. unfold sf_spec.no_viable_candidates. intros. inv H0.
- simpl in *. destruct a.
   + intuition. left. apply no_viable_candidates_cons. intuition.
     unfold sf_spec.no_viable_candidates. intros. inv H0; firstorder.
     right. unfold sf_spec.overvote in *. destruct H1. exists x.
     intuition. simpl. intuition.
   + destruct (forallb (eq_dec c) a) eqn:?.
     destruct (sf_imp.eliminated candidate reldec_candidate rec c) eqn:?; try congruence.
     rewrite eliminated_correct in *.  
     intuition. 
     * left. unfold sf_spec.no_viable_candidates. intros. simpl in *. destruct H0.  
       assert (candidate0 = c); subst; auto. rewrite forallb_forall in Heqb.
       specialize (Heqb candidate0). simpl in H2. destruct H2; auto.
       specialize (Heqb H0). apply reldec_correct_candidate in Heqb. auto.
       unfold sf_spec.no_viable_candidates in *.
       eapply H1; eauto.
     * right. clear H Heqb0.
       unfold sf_spec.overvote in *. 
       destruct H1. intuition. destruct H1. destruct H. intuition.
       exists x. simpl. intuition. left. intuition.
       subst.
       rewrite forallb_forall in Heqb. specialize (Heqb x0). 
Admitted.
 
    
Definition boolCmpToProp {A} (c : A -> A -> bool) :=
fun a b => match c a b with
           | true => True
           | false => False
end. 

Lemma insert_sorted : forall {A} c sorted (a : A),
    (forall a b, c a b = false -> c b a = true) ->
    Sorted (boolCmpToProp c) sorted ->
    Sorted (boolCmpToProp c) (sf_imp.insert c a sorted).
intros.
induction H0.
- simpl. auto.
- simpl.
  destruct (c a a0) eqn:?. 
  constructor. auto. constructor. unfold boolCmpToProp. rewrite Heqb. auto.
  constructor. auto.
  clear IHSorted H0.
  induction l.
  + simpl in *.
    constructor. unfold boolCmpToProp. apply H in Heqb. rewrite Heqb.
    auto.
  + simpl in *. destruct (c a a1) eqn:?. constructor. apply H in Heqb. 
    unfold boolCmpToProp. rewrite Heqb. auto.
    constructor; auto.
    unfold boolCmpToProp.
    apply H in Heqb. inv H1. unfold boolCmpToProp in H2. 
    auto.
Qed.
  
       
Lemma insertion_sort_sorted' : forall {A} (l : list A) (sorted : list A) c,
    (forall a b, c a b = false -> c b a = true) -> 
    Sorted (boolCmpToProp c) sorted ->
    Sorted (boolCmpToProp c) (sf_imp.insertionsort' c l sorted).   
Proof.
induction l.
+ intros. simpl. auto.
+ intros. simpl in *. apply IHl; auto.
  apply insert_sorted; auto.
Qed.      

Lemma insertion_sort_sorted : forall {A} (l : list A) c,
    (forall a b, c a b = false -> c b a = true) -> 
    Sorted (boolCmpToProp c) (sf_imp.insertionsort c l). 
intros.
apply insertion_sort_sorted'; auto.
Qed.

Lemma insert_permutation :
  forall {A} l2 l1  (a : A) c,
    Permutation l1 l2 ->
    Permutation (a :: l1) (sf_imp.insert c a l2).
Proof.
induction l2; intros. 
- apply Permutation_sym in H. apply Permutation_nil in H. subst. simpl in *. auto.
- simpl in *. destruct (c a0 a).
  constructor. auto.
  eapply Permutation_trans. instantiate (1:= (a0 :: a :: l2)).
  auto. rewrite perm_swap. constructor.
  apply IHl2. auto.
Qed.


Lemma insertion_sort_permutation' :
  forall {A} (le ls : list A) c sorted,
    Permutation ls sorted -> 
    Permutation (ls ++ le) (sf_imp.insertionsort' c le sorted).
Proof.
induction le; intros.
- simpl in *. rewrite app_nil_r. auto.
- simpl. rewrite <- Permutation_middle.
  rewrite app_comm_cons.
  apply IHle. apply insert_permutation. auto.
Qed.

Lemma insertion_sort_permutation :
  forall {A} (l : list A) c,
    Permutation l (sf_imp.insertionsort c l).
intros. rewrite <- app_nil_l at 1.
unfold sf_imp.insertionsort.
apply insertion_sort_permutation'. auto.
Qed.


Definition tb_func_to_Prop {c : Set} (f : list c -> option c) :=
fun l cd => match f l with 
         | Some x => x = cd
         | None => False
end.


Lemma in_split : forall A B (f : A) (l : list (A * B)), 
              In f (fst (split l)) -> 
              exists n : B, In (f, n) l.
Proof.
induction l; intros.
- simpl in *. inv H.
- simpl in *. destruct a. simpl in *.
  destruct (split l) eqn:?.
  simpl in *. destruct H. 
  + subst. eauto.
  + intuition. destruct H0. eauto. 
Qed.

Lemma first_choices_app : 
forall c l1 l2 x1 x2  r cnd, 
sf_spec.first_choices c r cnd l1 x1 ->
sf_spec.first_choices c r cnd l2 x2 ->
sf_spec.first_choices c r cnd (l1 ++ l2) (x1 + x2).
Proof.
induction l1; intros.
- simpl in *. inv H. simpl. auto.
- simpl in *. Print sf_spec.first_choices.
  inv H.
  + apply sf_spec.first_choices_selected. auto. fold plus.
    apply IHl1; auto.
  + apply sf_spec.first_choices_not_selected; auto.
Qed.

Lemma first_choices_app_gt :
forall c l1 l2 x1 x2 r cnd,
sf_spec.first_choices c r cnd l1 x1 ->
sf_spec.first_choices c r cnd (l1 ++ l2) (x2) ->
x2 >= x1.
Proof.
induction l1; intros.
- simpl in *. inv H. omega.
- simpl in *. inv H; inv H0; try congruence; try omega.
  eapply IHl1 in H5; eauto. omega.
  eapply IHl1; eauto.
Qed.

Lemma first_choices_perm : 
forall c l1 l2 x r cnd,
Permutation l1 l2 ->
sf_spec.first_choices c r cnd l1 x ->
sf_spec.first_choices c r cnd l2 x.
Proof.
induction l1; intros.
- apply Permutation_nil in H. subst. auto. 
- assert (exists l2s l23, l2 = l2s ++ (a :: l23)). 
  { eapply Permutation_in in H. instantiate (1 := a) in H.
    apply List.in_split in H. auto.
    constructor; auto. }
  destruct H1. destruct H1.
  subst.
  apply Permutation_cons_app_inv in H.
  inv H0.
  + eapply (IHl1 _ n' r cnd) in H; auto.
    clear - H H3.
    { generalize dependent x1. generalize dependent n'.
      induction x0; intros.
      - simpl in *. constructor; auto.
      - simpl in *. inv H. 
        + constructor; auto.
        + apply sf_spec.first_choices_not_selected; auto.
    }
  + eapply IHl1 in H; eauto.
    { clear - H H3.
      generalize dependent x1. generalize dependent x.
      induction x0; intros.
      - simpl in *. apply sf_spec.first_choices_not_selected; auto.
      - simpl in *. inv H.
        + constructor; auto.
        + apply sf_spec.first_choices_not_selected; auto.
    }
Qed.

Lemma rel_dec_refl : forall c, rel_dec c c = true.
Proof.
intros. apply rel_dec_correct. auto.
Qed.

Lemma increment_spec : forall m cd cds ct,
cds = (fst (split m)) ->
NoDup (cds) -> 
(In (cd, ct) m -> In (cd, S ct) (sf_imp.increment candidate _ m cd)) /\
(~In cd cds -> In (cd, 1) (sf_imp.increment candidate _ m cd)). 
Proof.
induction m; intros.
- simpl in *. intuition.
- simpl in *. destruct a. 
  destruct (split m) eqn:?.
  simpl in *. 
  destruct (in_dec rel_dec_p cd cds). 
  + subst.
    split.
    * { intros. simpl in *.
        unfold eq_dec.
        intuition.
        - inv H2.  rewrite rel_dec_refl.
          simpl. auto.
        - subst. clear -Heqp H2 H0.
          inv H0. assert (In cd l). apply in_split_l in H2. 
          simpl in H2. rewrite Heqp in *. auto.
          intuition.
        - inv H2. inv H0. intuition.
        - assert (c <> cd).
          intro. subst. inv H0. intuition.
          eapply rel_dec_neq_false in H.
          rewrite H. simpl. right.
          edestruct IHm. reflexivity.
          inv H0; auto.
          clear H4. auto. apply reldec_correct_candidate.
      } 
    * intuition.  
  + subst. simpl in *. inv H0. unfold eq_dec.  
    split. 
      * { intuition.
        - inv H0. intuition.
        - eapply rel_dec_neq_false in H. rewrite H. 
          edestruct IHm; eauto. simpl in *. auto.
          apply reldec_correct_candidate.
        }
      * intuition. eapply rel_dec_neq_false in H4. rewrite H4.
        simpl. 
        edestruct IHm; eauto.
        eapply reldec_correct_candidate.
Grab Existential Variables. exact O.
Qed.


Lemma increment_not_0 : forall running cd,
NoDup (fst (split running)) ->
~In (cd, 0) (sf_imp.increment candidate reldec_candidate running cd).
Proof.
induction running; intros; intro.
- unfold sf_imp.increment in *. simpl in *; intuition. congruence.
- simpl in *. destruct a. destruct (eq_dec c cd) eqn:?.
  + clear IHrunning. apply reldec_correct_candidate in Heqb. subst.
    simpl in *. destruct (split running) eqn:?. simpl in *. 
    inv H. intuition. congruence. apply in_split_l in H. 
    simpl in H. rewrite Heqp in H. simpl. intuition.
  + simpl in *. destruct (split running) eqn:?. simpl in *.
    apply neg_rel_dec_correct in Heqb. destruct H0.
    * inv H0. auto.
    * inv H. intuition. eapply IHrunning; eauto.
Qed.

Lemma increment_nodup' : forall running cd c,
~In c (fst (split running)) ->
c <> cd ->
~In c (fst (split (sf_imp.increment candidate reldec_candidate running cd))).
Proof.
induction running; intros.
- simpl in *. intuition.
- simpl in *.
  destruct a. 
  destruct (split running) eqn:?. simpl in H. intuition.
  destruct (eq_dec c0 cd) eqn:?.
  + simpl in *. rewrite Heqp in *. simpl in *. intuition.
  + simpl in *. destruct (split
                   (sf_imp.increment candidate reldec_candidate running cd)) eqn:?.
    simpl in *. intuition. eapply IHrunning; eauto. 
    rewrite Heqp0. simpl. auto.
Qed.

Lemma increment_nodup : forall running cd,
NoDup (fst (split running)) -> 
NoDup (fst (split (sf_imp.increment candidate reldec_candidate running cd))).
induction running; intros.
- simpl in *. constructor; auto. 
- simpl in *. destruct a. destruct (eq_dec c cd) eqn:?.
  + apply reldec_correct_candidate in Heqb. subst.
    simpl in *.
    destruct (split running) eqn:?. simpl in *. auto.
  + simpl in *. destruct ( split (sf_imp.increment candidate reldec_candidate running cd)) eqn:?.
    simpl.
    destruct (split running) eqn:?. simpl in *. inv H.
    eapply IHrunning in H3. instantiate (1:=cd) in H3. rewrite Heqp in H3.
    simpl in H3. constructor; auto. intro. apply neg_rel_dec_correct in Heqb.
    eapply increment_nodup'; eauto. instantiate (1:=running). 
    rewrite Heqp0. simpl. auto.
    rewrite Heqp. auto.
Qed.    

Lemma increment_neq : forall running c cd v,
In (c, v) running ->
c <> cd ->
In (c, v) (sf_imp.increment candidate reldec_candidate running cd).
Proof.
induction running; intros.
- inv H.
- destruct a.
  simpl in *.
  destruct (eq_dec c0 cd) eqn:?.
  + simpl in *. intuition.
    apply reldec_correct_candidate in Heqb. inv H1. subst. intuition.
  + simpl in *. intuition.
Qed.


Lemma tabulate_not_0 : forall l cd v running,
NoDup (fst (split running)) ->
In (cd, v) running ->
v <> 0 ->
~In (cd, 0)
   (sf_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl in *. intuition. apply H1.
  clear H1. induction running.
  + inv H0.
  + simpl in *. destruct a. destruct (split running) eqn:?. simpl in *.
    intuition.
    * inv H1. inv H0. auto.
    * inv H1. inv H. intuition. apply in_split_l in H0. simpl in *.
      rewrite Heqp in *. simpl in *. intuition.
    * inv H. inv H0. apply in_split_l in H1. rewrite Heqp in *. simpl in *.
      intuition.
    * inv H. intuition.
- simpl in *. destruct a. intro. intuition.
  destruct (rel_dec_p c cd). 
  + subst.
    eapply IHl in H2; auto.
    * apply increment_nodup. auto.
    * instantiate (1:=S v). edestruct increment_spec. reflexivity.
      apply H. apply H3. auto.
    * intuition.
  + eapply IHl in H2; auto.
    * apply increment_nodup; auto.
    * instantiate (1:=v). edestruct increment_spec. reflexivity.
      apply H. apply increment_neq; auto.
    * auto.
  + eapply IHl in H0; auto.
Grab Existential Variables. apply 0. apply c. (*ugh*)
Qed.
   
Lemma opt_eq_dec : forall A,
(forall (a b : A), {a = b} + {a <> b}) ->
forall (a b : option A), {a = b} + {a <> b}.
Proof.
intros.
destruct a, b; auto.
specialize (X a a0). destruct X. subst. auto. right.
intro. inv H. auto.
right. intro. congruence.
right. congruence.
Qed.

Lemma opt_eq_dec_cand : 
forall (a b : option candidate), {a = b} + {a <> b}.
Proof.
apply opt_eq_dec. apply rel_dec_p.
Qed.

Lemma NoDup_In_fst :
forall A B l (a :A) (b :B) c,
NoDup (fst (split l)) ->
In (a, b) l ->
In (a, c) l ->
b = c.
Proof.
induction l; intros.
- inv H0.
- simpl in *.
  destruct (split l) eqn:?.
  destruct a. intuition; try congruence.
  + simpl in *. inv H2. inv H. apply in_split_l in H0. simpl in H0. 
    rewrite Heqp in *. intuition.
  + simpl in *. inv H. inv H0. 
    apply in_split_l in H2. simpl in*. rewrite Heqp in *.
    intuition.
  + eapply IHl; eauto. simpl. simpl in H. inv H. auto.
Qed.

Lemma tab_inc_s : forall cd ct l running running' cr,
NoDup (fst (split running)) ->
NoDup (fst (split running')) ->
In (cd, S ct)
   (sf_imp.tabulate'' candidate reldec_candidate l running') ->
In (cd, cr) running ->
In (cd, (S cr)) running' ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl in *. 
  assert (cr = ct).
  eapply NoDup_In_fst in H3. instantiate (1:=S ct) in H3. congruence.
  auto. auto. subst. auto.
- simpl in *.
  destruct a. 
  + destruct (rel_dec_p cd c).
    * subst. eapply IHl.
      apply increment_nodup. auto. 
      apply increment_nodup. apply H0.
      eauto. 
      eapply increment_spec in H2; eauto.
      eapply increment_spec in H3; eauto.
    * eapply increment_neq in H2; eauto.
      eapply increment_neq in H3; eauto.
      eapply IHl.
      apply increment_nodup. auto.
      apply increment_nodup. apply H0.
      apply H1.
      eauto.
      eauto.
  + eapply IHl; eauto.
Qed.


Ltac copy H :=
match type of H with 
?P => assert P by exact H end.

Lemma increment_neq' : forall running cd ct  c,
In (cd, ct) (sf_imp.increment candidate reldec_candidate running c) ->
c <> cd ->
In (cd, ct) running.
Proof.
induction running; intros.
- simpl in H. intuition. congruence.
- simpl in *. destruct a.
  + destruct (eq_dec c0 c) eqn:?.
    apply rel_dec_correct in Heqb. subst.
    simpl in *. intuition. inv H1. intuition.
    simpl in *. intuition.
    right. eapply IHrunning; eauto.
Qed.

Lemma tabulate''_same : forall cd l running running' cr ct,
NoDup (fst (split running)) ->
NoDup (fst (split running')) ->
In (cd, cr) running ->
In (cd, cr) running' ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running) ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running').
Proof.
induction l; intros.
- simpl in *. 
  assert (cr = ct).
  eapply NoDup_In_fst. apply H.
  apply H1. apply H3. subst.
  auto.
- simpl in *.
  destruct a.
  + destruct (rel_dec_p cd c).
    * eapply IHl.
      apply increment_nodup. apply H.
      apply increment_nodup. auto. 
      subst.
      eapply increment_spec in H1. apply H1.
      auto. auto.
      subst. eapply increment_spec in H2; eauto.
      eauto.
    * eapply IHl.
      apply increment_nodup. apply H.
      apply increment_nodup. auto.
      eapply increment_neq in n. apply n. eauto.
      eapply increment_neq in n.
      eauto. auto.
      eauto.
  + eapply IHl; eauto.
Qed.

Lemma tabulate''_same_notin : forall cd ct l running running',
NoDup (fst (split running)) ->
NoDup (fst (split running')) ->
~In cd (fst (split running)) ->
~In cd (fst (split running')) ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running) ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running').
Proof.
induction l; intros.
- simpl in *. intuition. 
  apply in_split_l in H3. simpl in H3. intuition.
- simpl in *.
  destruct a; try solve [eapply IHl; eauto].
  destruct (rel_dec_p cd c).
  + subst. eapply increment_spec in H1; eauto.
    eapply increment_spec in H2; eauto.
    eapply (tabulate''_same _ _ _ _ _ _ _ _ _ H2).
    eauto. 
  + eapply IHl. apply H.
    apply increment_nodup. auto. auto. apply increment_nodup'; eauto.
    eapply IHl in H3. eauto. 
    apply increment_nodup. auto. auto. apply increment_nodup'; eauto.  
    auto. Grab Existential Variables. auto.
    apply increment_nodup. auto. apply increment_nodup. auto.
Qed.

Lemma tab_inc_s_l :
forall l cd ct running,
In (cd, S ct) (sf_imp.tabulate'' candidate reldec_candidate l
               (sf_imp.increment candidate reldec_candidate running cd)) ->
~ In cd (fst (split running)) ->
NoDup (fst (split running)) ->
In (Some cd) l ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- inv H2.
- simpl in *. destruct a.
  destruct (rel_dec_p cd c). 
  + subst. clear H2.
    simpl in *. eapply increment_spec in H0; auto.
    copy H0.
    eapply increment_spec in H0; auto.
    eapply tab_inc_s. apply increment_nodup. auto. apply increment_nodup.
    apply increment_nodup. eauto. eauto. eauto. eauto.
    apply increment_nodup. auto. 
  + destruct H2. congruence. 
    eapply tabulate''_same_notin.
    eauto. apply increment_nodup. auto.
    auto.
    apply increment_nodup'; auto.
    eapply IHl; eauto.
    eapply (tabulate''_same) in H.
    apply H. apply increment_nodup. apply increment_nodup.
    auto. apply increment_nodup. auto.
    apply increment_neq; auto. eapply increment_spec in H0; eauto.
    eapply increment_spec in H0; eauto.
  + intuition. congruence.
Qed.

Lemma tabulate_not_in_l :
forall l cd ct running,
NoDup (fst (split running)) ->
In (cd, ct) running ->
~In (Some cd) l ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl. auto.
- simpl in *.
  destruct a; intuition; try congruence.
  eapply IHl; eauto. apply increment_nodup. auto.
  apply increment_neq; auto. intuition. subst. auto.
Qed.

Lemma tabulate_nodup :
forall l running,
NoDup (fst (split running)) -> 
NoDup (fst (split (sf_imp.tabulate'' candidate reldec_candidate l running))).
Proof.
induction l; intros.
- simpl.  auto.
- simpl in *.
  destruct a.
  + apply IHl. apply increment_nodup; auto.
  + apply IHl. auto.
Qed.


Lemma selected_not_in :
forall  ef l cd r l0, 
~(In (Some cd ) l) ->
sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate r) ef) =
         (l, l0) ->
sf_spec.first_choices candidate (in_record r) cd ef 0.
Proof.
induction ef; intros.
- simpl in *. inv H0. constructor.
- simpl in *. 
  destruct (sf_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  + destruct p. destruct (sf_imp.option_split
                            (map (sf_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    simpl in *. inv H0. simpl in *.
    intuition.
    apply next_ranking_selected in Heqo.
    constructor.
    intro. eapply sf_spec.selected_candidate_unique in Heqo; eauto.
    subst; auto.
    eapply IHef; eauto.
  + destruct (sf_imp.option_split
              (map (sf_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    inv H0.
    simpl in *.
    apply sf_spec.first_choices_not_selected.
    intro. intuition. unfold sf_spec.selected_candidate in H0.
    destruct H0. apply next_ranking_eliminated in Heqo.
    unfold sf_spec.continuing_ballot in H. intuition.
    eapply IHef; eauto.
Qed.

Lemma increment_same_s : 
forall c running,
NoDup (fst (split running)) ->
exists n, In (c, S n) (sf_imp.increment candidate _ running c).
intros. 
destruct (in_dec rel_dec_p c (fst (split running))).
apply in_split in i. destruct i.
exists x. eapply increment_spec in H; eauto.
destruct H. apply H. auto.
exists 0. eapply increment_spec in n; eauto. apply 0.
Qed.


Lemma tabulate''_first_choices : forall ef cd ct es running r
(NODUP : NoDup (fst (split running))),
In (cd, ct) (sf_imp.tabulate'' candidate _ 
                               (fst (sf_imp.option_split
                                      (map (sf_imp.next_ranking candidate reldec_candidate r)
                                           ef))) running) -> 
(forall cnd, ~In cnd (fst (split running)) -> sf_spec.first_choices candidate (in_record r) cnd es 0) ->
Forall (fun x => let (cnd, n) := (x: candidate * nat) 
                 in sf_spec.first_choices candidate (in_record r) cnd es n) running ->
sf_spec.first_choices candidate (in_record r) cd (es ++ ef) ct. 
Proof.
induction ef; intros.
- simpl in *. rewrite Forall_forall in *. specialize (H1 _ H). simpl in H1.
  rewrite app_nil_r.  auto.
- simpl in H. 
  assert (Permutation (a :: (es ++ ef)) (es ++ a :: ef)). 
  apply Permutation_middle.
  eapply first_choices_perm; eauto. clear H2.
  destruct (sf_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  +  destruct p. destruct (sf_imp.option_split
                     (map (sf_imp.next_ranking candidate reldec_candidate r)
                          ef)) eqn:?. simpl in *. 
     apply next_ranking_selected in Heqo.
     destruct (rel_dec_p c cd). 
     * subst. 
       { destruct ct. 
         - clear - H NODUP.
           assert (X := increment_same_s cd running NODUP).
           destruct X.
           exfalso. eapply tabulate_not_0; [ | | | apply H]; eauto.
           apply increment_nodup. auto.
         - constructor. auto. 
           destruct (in_dec rel_dec_p cd (fst (split running))).
           + eapply IHef; eauto.
             edestruct in_split. apply i.
             eapply tab_inc_s; auto.
             apply increment_nodup. eauto.
             rewrite Heqp. simpl. eauto.
             apply H2. eapply increment_spec in H2; eauto.
           + destruct (in_dec opt_eq_dec_cand (Some cd) l).
             * eapply IHef; eauto.
               rewrite Heqp. simpl.
               apply tab_inc_s_l; auto.
             * copy n. eapply increment_spec in n; eauto.
               eapply tabulate_not_in_l in n; eauto.
               assert (1 = (S ct)). eapply NoDup_In_fst; [ | eauto | eauto ].
               apply tabulate_nodup. apply increment_nodup. auto.
               inv H3. change 0 with (0 + 0). 
               { apply first_choices_app. 
                 - apply H0. auto.
                 - eapply selected_not_in; eauto.
               } 
               apply increment_nodup; auto.
       }
     * apply sf_spec.first_choices_not_selected. intro.
       apply n. eapply sf_spec.selected_candidate_unique; eauto.
       { destruct (in_dec rel_dec_p cd (fst (split running))).
         - copy i. apply in_split in H2. destruct H2.
           eapply IHef; eauto.
           rewrite Heqp. simpl. eapply tabulate''_same in H; eauto.
           eauto.
           apply increment_nodup. auto. 
           apply increment_neq; auto.
         - eapply IHef; eauto.
           rewrite Heqp. simpl.
           eapply tabulate''_same_notin in H.
           eauto. apply increment_nodup. auto.
           auto. intro.
           apply in_split in H2.
           destruct H2. 
           apply n0.
           eapply increment_neq' in H2. 
           apply in_split_l in H2. auto.
           auto. auto.
       }
  + destruct ( sf_imp.option_split
                 (map (sf_imp.next_ranking candidate reldec_candidate r)
                      ef)) eqn:?.
    simpl in *. 
    apply next_ranking_eliminated in Heqo.
    apply sf_spec.first_choices_not_selected.
    intro. unfold sf_spec.selected_candidate in H2.
    intuition.
    eapply IHef; eauto. rewrite Heqp. simpl. auto.
Qed.
Print sf_imp.tabulate.

Lemma tabulate'_first_choices : forall l cd ct  r,
In (cd, ct) (sf_imp.tabulate' _ _ (fst (sf_imp.option_split
                                      (map (sf_imp.next_ranking candidate reldec_candidate r)
                                           l)))) -> 
sf_spec.first_choices candidate (in_record r) cd (l) ct. 
Proof.
intros.
rewrite <- app_nil_l at 1.
eapply tabulate''_first_choices in H. eauto.
constructor.
intros. constructor.
constructor.
Qed.

Lemma tabulate_correct : forall rec election rs election',
sf_imp.tabulate candidate _ rec election = (rs, election') ->
Forall (fun (x: (candidate * nat)) => let (cd, fc) := x in
                 sf_spec.first_choices candidate (in_record rec) cd election fc) rs.
Proof.
intros.
unfold sf_imp.tabulate in H. destruct (sf_imp.option_split
             (map (sf_imp.next_ranking candidate reldec_candidate rec)
                election)) eqn:?.
assert (PRM := insertion_sort_permutation (sf_imp.tabulate' candidate reldec_candidate l)
                                          (sf_imp.cnlt candidate)).
rewrite Forall_forall. intros. destruct x. destruct ((sf_imp.insertionsort (sf_imp.cnlt candidate)
         (sf_imp.tabulate' candidate reldec_candidate l),
      sf_imp.drop_none l0)) eqn:?. inv H.
inv Heqp0.
apply Permutation_sym in PRM.
eapply Permutation_in in PRM; eauto.
assert (l = fst (sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate rec) election))).
rewrite Heqp. auto.  subst.
clear H0.
apply tabulate'_first_choices in PRM. auto.
Qed.

Lemma leb_false :
forall n0  n,
NPeano.leb n0 n = false ->
n <= n0.
Proof. 
induction n0; intros.
- inv H.
- simpl in *.  destruct n.
  omega. 
  apply IHn0 in H. omega.
Qed.


Lemma tabulate_sorted : 
forall rec election rs election',
sf_imp.tabulate _ _ rec election = (rs, election') ->
Sorted (boolCmpToProp (sf_imp.cnlt candidate)) rs.
Proof.
intros.
intros.
unfold sf_imp.tabulate in H. destruct (sf_imp.option_split
             (map (sf_imp.next_ranking candidate reldec_candidate rec)
                election)) eqn:?.
inv H. apply insertion_sort_sorted.
intros. unfold sf_imp.cnlt. destruct b. 
destruct a. simpl in *. apply leb_false in H.
apply NPeano.leb_le. auto.
Qed.

Lemma tabulate_continuing :
forall election rs election' rec,
sf_imp.tabulate _ _ rec election = (rs, election') ->
Forall (fun x =>~ in_record rec x)(fst (split rs)) .
Proof.
  intros. 
unfold sf_imp.tabulate in *.
Check sf_imp.increment.

Lemma increment_not_eliminated : 
forall vs c rec,
~(in_record rec c) ->
Forall (fun cd =>  ~(in_record rec cd)) (fst (split vs)) ->
Forall (fun cd => ~(in_record rec cd)) (fst (split (sf_imp.increment candidate _ vs c))).
Proof.
induction vs; intros.
- simpl in *. auto.
- simpl in *. rewrite Forall_forall in *.
  intros. destruct a.
  destruct (eq_dec c0 c) eqn:?. 
  + simpl in *. destruct (split vs) eqn:?.
    simpl in *. intuition. subst. apply reldec_correct_candidate in Heqb.
    subst. intuition.
    specialize (H0 x). intuition.
  + simpl in *. destruct (split (sf_imp.increment candidate reldec_candidate vs c)) eqn:?.
    simpl in *. intuition.
    * subst. specialize (H0 x). 
      destruct (split vs) eqn:?. simpl in *. intuition.
    * eapply IHvs in H; eauto.
      rewrite Forall_forall in H.
      eapply H; eauto.       
      rewrite Heqp. auto.
      rewrite Forall_forall. intros.
      specialize (H0 x0). destruct (split vs).
      simpl in *. intuition.
Qed.


Lemma tabulate''_continuing : forall ef cd ct  running r,
In (cd, ct) (sf_imp.tabulate'' candidate _ 
                               (fst (sf_imp.option_split
                                      (map (sf_imp.next_ranking candidate reldec_candidate r)
                                           ef))) running) -> 
Forall (fun x => ~(in_record r x)) (fst (split running)) ->
~(in_record r cd). 
Proof.
induction ef; intros.
- simpl in *. rewrite Forall_forall in H0.
  specialize (H0 (cd)). intuition. apply H0; auto.
  apply in_split_l in H. simpl in H. auto.
- simpl in *. destruct ( sf_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  + destruct p. apply next_ranking_selected in Heqo.
    destruct (sf_imp.option_split
                (map (sf_imp.next_ranking candidate reldec_candidate r)
                     ef)) eqn:?. simpl in *.
    apply sf_spec.selected_candidate_not_eliminated in Heqo. 
    eapply increment_not_eliminated in Heqo; eauto. 
    eapply IHef. rewrite Heqp. simpl. eauto.
    auto.
  + destruct (sf_imp.option_split
                (map (sf_imp.next_ranking candidate reldec_candidate r)
                     ef)) eqn:?.
    simpl in *.
    eapply IHef. rewrite Heqp. simpl. eauto.
    eauto.
Qed.

Lemma tabulate''_first_choices_complete : forall ef cd ct es running r
(NODUP : NoDup (fst (split running))), 
(forall cnd cnt, 
cnt <> 0 ->
sf_spec.first_choices candidate (in_record r) cnd es cnt -> In (cnd, cnt) running) ->
ct <> 0 -> 
sf_spec.first_choices candidate (in_record r) cd (es ++ ef) ct ->
In (cd, ct) (sf_imp.tabulate'' candidate _ 
                               (fst (sf_imp.option_split
                                      (map (sf_imp.next_ranking candidate reldec_candidate r)
                                           ef))) running). 
Proof.
induction ef; intros.
- simpl in *. rewrite app_nil_r in *. intuition.  
Admitted.
(*
- simpl in *. 
  destruct ( sf_imp.next_ranking candidate reldec_candidate r a ) eqn:?.
  + destruct p. simpl.
    destruct (sf_imp.option_split
                (map (sf_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    simpl in *. assert (Permutation (es ++ a :: ef) (a :: (es ++ ef))).
    rewrite Permutation_middle. auto.
    eapply first_choices_perm in H1; eauto.
    clear H0.
    inv H1.
    * apply next_ranking_selected in Heqo; auto.
      eapply sf_spec.selected_candidate_unique in Heqo; eauto. subst.
      assert (l = fst ( sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate r) ef))).
     rewrite Heqp. auto.
     subst. 
Admitted. *)

Lemma tabulate'_first_choices_complete : forall l cd ct r,
ct <> 0 ->
sf_spec.first_choices _ (in_record r) cd l ct ->
In (cd, ct) (sf_imp.tabulate' _ _ 
   (fst (sf_imp.option_split (map (sf_imp.next_ranking _ _ r) l)))).
Proof.
intros.
unfold sf_imp.tabulate'.
rewrite <- (app_nil_l l) in H0.
eapply tabulate''_first_choices_complete; eauto; try solve [constructor].
intros. inv H2. congruence.
Qed.

Lemma tabulate_first_choices_complete : forall l cd ct r,
ct <> 0 -> 
sf_spec.first_choices _ (in_record r) cd l ct ->
In (cd, ct) (fst (sf_imp.tabulate _ _ r l)). 
  intros.
  unfold sf_imp.tabulate.
  destruct (sf_imp.option_split
               (map (sf_imp.next_ranking candidate reldec_candidate r) l)) eqn:?.
  eapply Permutation_in.
  apply insertion_sort_permutation.
  assert (l0 = fst (sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate r) l))).
  rewrite Heqp. auto.
  subst.
  eapply tabulate'_first_choices_complete. auto.
  auto.
Qed.


Lemma cnlt_trans : Relations_1.Transitive (boolCmpToProp (sf_imp.cnlt candidate)).
Proof.
intro. intros.
destruct x, y, z.
unfold boolCmpToProp in *. simpl in *.
generalize dependent n0. revert n1.
induction n; intros.
simpl in *. auto.
simpl in *. destruct n0. inv H.
simpl in *.
destruct n1. auto.
eapply IHn; eauto.
Qed.


Lemma get_bottom_votes_is_loser :
forall election rec losers rs election'
(ELIMO : forall c, sf_spec.participates _ c election -> sf_spec.first_choices _ (in_record rec) c election 0 ->
           (in_record rec c)),
sf_imp.tabulate _ _ rec election = (rs, election') ->
sf_imp.get_bottom_votes  _ rs = losers ->
Forall (sf_spec.is_loser candidate (in_record rec) election) losers.
Proof.
intros.
destruct (sf_imp.tabulate _ _ rec election) eqn:?. inv H.
destruct rs. 
- simpl in *. auto.
- simpl in *. destruct p. rewrite <- EqNat.beq_nat_refl.
  simpl. rewrite Forall_forall.
  intros. simpl in *.
  destruct H. 
  + subst. assert (SRTD := tabulate_sorted _ _ _ _ Heqp).
    apply Sorted_StronglySorted in SRTD.
    *    assert (CRCT := tabulate_correct _ _ _ _ Heqp).
         rewrite Forall_forall in CRCT.
         specialize (CRCT (x, n)). intuition.
         simpl in *. intuition. clear H0.
         inv SRTD.
         unfold sf_spec.is_loser.
         { repeat split.
           - unfold sf_imp.tabulate in Heqp. unfold
                                           sf_imp.tabulate' in Heqp.
             destruct (sf_imp.option_split
                         (map (sf_imp.next_ranking candidate reldec_candidate rec)
                              election)) eqn:?.
             inv Heqp.
             assert (PRM := insertion_sort_permutation ((sf_imp.tabulate'' candidate reldec_candidate l [])) 
                                                       (sf_imp.cnlt candidate)).
             eapply Permutation_sym in PRM.
             eapply Permutation_in in PRM.
             instantiate (1 := (x, n)) in PRM.
             eapply tabulate''_continuing. instantiate (1 := nil). instantiate (1 := election). 
             erewrite Heqp0. simpl. eauto.
             constructor.
             rewrite H0. constructor. auto.
           - admit. (*TODO: need a lemma*)
           - intros.
             assert (n = n0); [ | subst n0 ].
             { eapply sf_spec.sf_first_choices_unique in H0; [ | apply H1]. auto. }
             rewrite Forall_forall in H3.
             destruct H.
             unfold sf_spec.participates in H5.
             destruct H5.
             destruct H5. destruct H6. destruct H6.
             destruct (NPeano.Nat.eq_dec n m). omega.
             cut (In (c', m) rs). intros.
             apply H3 in H8. unfold boolCmpToProp in H8.
             simpl in *. destruct (NPeano.leb n m) eqn:?; try contradiction.
             apply NPeano.leb_le in Heqb. auto. 
             edestruct (rel_dec_p c' x).
             subst.
             eapply sf_spec.sf_first_choices_unique in H4; [ | apply H1]. intuition.
             apply tabulate_first_choices_complete in H4. 
             rewrite Heqp in H4. simpl in H4. 
             destruct H4. congruence. auto.
             intro.
             subst.
             eapply ELIMO in H4. auto.
             admit. (*same lemma as admit above*)
         } 
    *  apply cnlt_trans.
  + assert (In (x, n) (filter
              (fun x0 : candidate * nat =>
               let (_, v') := x0 in EqNat.beq_nat n v') rs)).
    rewrite filter_In. split.
    * rewrite in_map_iff in H. destruct H. destruct x0. simpl in H. intuition.
      subst. rewrite filter_In in H1. intuition.
      apply EqNat.beq_nat_true in H0. subst.
      auto.
    * symmetry. apply EqNat.beq_nat_refl.
    * clear H.
      rewrite filter_In in H0. destruct H0.
      assert (SRTD := tabulate_sorted _ _ _ _ Heqp).
      apply Sorted_StronglySorted in SRTD.
      assert (CRCT := tabulate_correct _ _ _ _ Heqp).
      rewrite Forall_forall in CRCT.
      inv SRTD.
      simpl in *. specialize (CRCT ((x, n))).
      intuition. clear H1.
      unfold sf_spec.is_loser.
      split.
      split.
      admit. (*TODO*)
      admit.
      intros ? ? ? [??] ? ?.
      eapply sf_spec.sf_first_choices_unique in H5; eauto. subst.
      rewrite Forall_forall in H4.
      specialize (H4 (c', m)).
      destruct (rel_dec_p c c').
      subst.
      assert (CRCT := tabulate_correct _ _ _ _ Heqp).
      rewrite Forall_forall in CRCT.
      specialize (CRCT (c', n)). simpl in CRCT. intuition.
      clear H8.
      eapply sf_spec.sf_first_choices_unique in H7; eauto.
      subst.
      auto.
      assert (In (c', m) rs).
      apply tabulate_first_choices_complete in H7.
      rewrite Heqp in *. simpl in H7. destruct H7.
      inv H5. intuition.
      auto.
      intro.
      subst.
      apply ELIMO in H7; auto.
      intuition.
      unfold boolCmpToProp in H8. simpl in H8.
      destruct (NPeano.leb n m) eqn:?; intuition.
      apply NPeano.Nat.leb_le in Heqb. auto.
      apply cnlt_trans.
Qed.
      
      
      




Lemma selected_not_eliminated 
  unfold sf_spec.exhausted_ballot in H1. 
  Check next_ranking_selected.
Fixpoint find_eliminated' (eliminated : list candidate) (votes : list (candidate * nat)) (sum : nat) :=


Lemma run_election'_correct : forall fuel election winner tb rec rec',
    sf_imp.run_election' candidate _ tb election rec fuel = (Some winner, rec') ->
    sf_spec.winner candidate election (in_record []) winner.
induction fuel; intros.
simpl in *. congruence.
simpl in *.
Admitted.



Theorem run_election_correct : forall election winner tb rec, 
    sf_imp.run_election candidate _ tb election = (Some winner, rec) ->
    sf_spec.winner candidate (tb_func_to_Prop tb) election (in_record []) winner.
intros. unfold sf_imp.run_election in H. apply run_election'_correct in H. auto.
Qed.


