Require Undecidability.Shared.Dec Undecidability.Shared.ListAutomation.
Require Import Setoid Morphisms.
Require Import Undecidability.Synthetic.Definitions Lia List NPeano.
From Undecidability.Shared Require Import mu_nat equiv_on Pigeonhole Dec.
Import ListNotations.

Definition lists {X} (l : list X) (p : X -> Prop) := forall x, p x <-> List.In x l. 
Definition exhausts {X} (l : list X) (p : X -> Prop) := forall x, p x -> List.In x l.

Definition listable {X} (p : X -> Prop) := exists l, lists l p.
Definition exhaustible {X} (p : X -> Prop) := exists l, exhausts l p.

Lemma lists_exhausts {X} (l : list X) p : 
  lists l p -> exhausts l p.
Proof.
  firstorder.
Qed.

Lemma listable_exhaustible {X} {p : X -> Prop} : 
  listable p -> exhaustible p.
Proof.
  firstorder.
Qed.

Lemma filter_ex {X} l (p : X -> Prop) :
   ~~ exists l', forall x, In x l' <-> In x l /\ p x.
Proof.
  induction l as [ | x]; intros H.
  - apply H. exists []. firstorder.
  - apply IHl. intros (l' & IH).
    assert (Hx : ~~ (p x \/ ~ p x)) by tauto.
    apply Hx. clear Hx. intros [Hx | Hx].
    + apply H. exists (x :: l'). cbn. setoid_rewrite IH.
      clear - Hx. firstorder congruence.
    + apply H. exists l'. cbn. setoid_rewrite IH.
      clear - Hx. firstorder congruence.
Qed.

Lemma LEM_DN : (forall P, P \/ ~P) -> forall P, ~~ P -> P.
Proof.
  intros H P. specialize (H P). tauto.
Qed.

Lemma exhaustible_listable X (p : X -> Prop) : 
  exhaustible p -> ~~ listable p.
Proof.
  intros [l Hl].
  pose proof (filter_ex l p) as Hfilter.
  intros H1. apply Hfilter. intros [l' Hl'].
  apply H1. exists l'. intros x.
  rewrite Hl'. firstorder.
Qed.

Lemma LEM_exhaustible_listable :
  (forall P, P \/ ~ P) -> (forall X (p : X -> Prop), exhaustible p -> listable p).
Proof.
  intros H X p Hp. apply (LEM_DN H), exhaustible_listable, Hp.
Qed.

Lemma exhaustible_listable_LEM :
  (forall p : unit -> Prop, exhaustible p -> listable p) -> forall P, P \/ ~ P.
Proof.
  intros H P.
  specialize (H (fun _ => P)) as [l Hl].
  - exists (cons tt nil). intros []. firstorder.
  - specialize (Hl tt). cbn in Hl. rewrite Hl. clear.
    destruct l as [ | []]; firstorder.
Qed.

Lemma exhaustible_listable_LEM_iff :
  (forall X (p : X -> Prop), exhaustible p -> listable p) <-> forall P, P \/ ~ P.
Proof.
  split.
  - intros H. apply exhaustible_listable_LEM, H.
  - apply LEM_exhaustible_listable.
Qed.

(** ** Infinite types and predicates  *)

Lemma non_exhaustible_non_listable {X} (p : X -> Prop) :
  ~ exhaustible p -> ~ listable p.
Proof.
  intros H1 H2. apply H1, listable_exhaustible, H2.
Qed.

Lemma non_listable_non_exhaustible {X} (p : X -> Prop) :
  ~ listable p -> ~ exhaustible p.
Proof.
  intros Hl [l H].
  pose proof (filter_ex l p) as Hfilter.
  apply Hfilter. intros [l' Hl'].
  apply Hl. exists l'. intros x.
  rewrite Hl'. firstorder.
Qed.

Lemma non_listable_non_exhaustible_iff {X} (p : X -> Prop) :
  ~ listable p <-> ~ exhaustible p.
Proof.
  split. 
  apply non_listable_non_exhaustible.
  apply non_exhaustible_non_listable.
Qed.

Definition generative {X} (p : X -> Prop) :=
  forall l : list X, exists x, p x /\ ~ In x l.

Lemma generative_inhabited {X} (p: X -> Prop):
  generative p -> exists x, p x.
Proof.
  intros H1. specialize (H1 []) as [x [H _]].
  eauto.
Qed.

Lemma nonfinite_inhabited {X} (p: X -> Prop):
  (~ exhaustible p) -> ~~ exists x, p x.
Proof.
  intros H1 H2.
  apply H1. exists nil. intros x px. apply H2. exists x. exact px.
Qed.

Lemma generative_non_exhaustible {X} (p : X -> Prop) :
  generative p -> ~ exhaustible p.
Proof.
  intros H [l Hl]. destruct (H l) as (x & H1 & H2).
  apply H2, Hl, H1.
Qed.

Lemma in_ldec {X} (x : X) l (H : forall x1 x2 : X, x1 = x2 \/ x1 <> x2) :
 In x l \/ ~ In x l.
Proof. 
  induction l as [ | x' l [IH |IH]]; firstorder.
Qed.

Lemma non_finite_spec {X} (p : X -> Prop) (D : forall x1 x2 : X, x1 = x2 \/ x1 <> x2) :
  ~ exhaustible p <-> forall l, ~~ exists x, p x /\ ~ In x l.
Proof.
  split.
  - intros H l. intros Hl. apply H. exists l. intros x Hx.
    destruct (in_ldec x l D); firstorder.
  - firstorder.
Qed.

Lemma non_finite_nat (p : nat -> Prop) :
  ~ exhaustible p <-> forall n, ~~ exists m, m >= n /\ p m.
Proof.
  rewrite non_finite_spec. 2: intros; decide (x1 = x2); tauto.
  split.
  - intros H n. specialize (H (seq 0 n)).
    cunwrap. destruct H as (x & H1 & H2).
    cprove exists x. split; eauto.
    assert (x >= n \/ x < n) as [H | H] by lia; eauto.
    destruct H2. eapply in_seq. lia.
  - intros H l. specialize (H (1 + list_max l)).
    cunwrap. destruct H as (m & H1 & H2).
    cprove exists m. split; eauto.
    assert (list_max l <= list_max l) as ? % list_max_le by lia.
    rewrite Forall_forall in H0.
    intros ? % H0. lia.
Qed.

Lemma non_exhaustible_generative {X} (p : X -> Prop) :
  (forall P, P \/ ~ P) -> ~ exhaustible p -> generative p.
Proof.
  intros lem He l. apply (LEM_DN lem). apply non_finite_spec.
  - intros. eapply lem.
  - exact He.
Qed.

Lemma generative_ext {X} :
  Proper ((@pointwise_relation _ _ iff) ==> iff) (@generative X).
Proof.
  intros p1 p2 H. red in H.
  split; intros Hg l; destruct (Hg l) as [x Hx]; exists x; firstorder.
Qed.

Lemma generative_nat (p : nat -> Prop) :
  generative p <-> forall n, exists m, m >= n /\ p m.
Proof.
  split.
  - intros H n. specialize (H (seq 0 n)) as (x & H1 & H2).
    exists x. split; eauto.
    assert (x >= n \/ x < n) as [H | H] by lia; eauto.
    destruct H2. eapply in_seq. lia.
  - intros H l. specialize (H (1 + list_max l)) as (m & H1 & H2).
    exists m. split; eauto.
    assert (list_max l <= list_max l) as ? % list_max_le by lia.
    rewrite Forall_forall in H0.
    intros ? % H0. lia.
Qed.

Definition unbounded {X} (p : X -> Prop) :=
  forall n, exists l, length l = n /\ NoDup l /\ forall x, In x l -> p x.

Lemma generative_unbounded {X} (p : X -> Prop) :
  generative p -> unbounded p.
Proof.
  intros Hgen n. induction n as [ | n (l & H1 & H2 & H3)].
  - exists []. firstorder. econstructor.
  - destruct (Hgen l) as [x [Hx1 Hx2]].
    exists (x :: l). repeat split. 
    + cbn. congruence.
    + now econstructor.
    + intros x0 [-> | ]; eauto.
Qed.

Lemma unbounded_generative {X} (p : X -> Prop) (H : forall x1 x2 : X, x1 <> x2 \/ ~ x1 <> x2) :
  unbounded p -> generative p.
Proof.
  intros Ha l. specialize (Ha (length l + 1)) as (l' & H1 & H2 & H3).
  eapply (@pigeonhole _ l' l) in H2 as (x0 & Hx0 & Hx1).
  - exists x0. eauto.
  - eauto.
  - lia.
Qed.

Lemma unbounded_weakly_unbounded {X} (p : X -> Prop) :
  unbounded p -> forall n, ~~ exists l, length l = n /\ NoDup l /\ forall x, In x l -> p x.
Proof.
  firstorder.
Qed.

Lemma weakly_unbounded_non_finite {X} (p : X -> Prop) :
  (forall n, ~~ exists l, length l = n /\ NoDup l /\ forall x, In x l -> p x) -> ~ exhaustible p.
Proof.
  intros Ha [l Hl]. specialize (Ha (length l + 1)).
  apply Ha. intros (l' & H1 & H2 & H3).
  eapply (pigeonhole_constructive l' l) in H2. 2:lia. apply H2. intros (x0 & Hx0 & Hx1).
  firstorder.
Qed.


Lemma unbounded_non_finite {X} (p : X -> Prop) :
  unbounded p -> ~ exhaustible p.
Proof.
  intros H.
  eapply weakly_unbounded_non_finite, unbounded_weakly_unbounded, H.
Qed.

(* 
Lemma generative_even :
  generative (fun n : nat => Nat.even n = true).
Proof.
  intros l. exists (2 * S (list_max l)). split.
  - now rewrite Nat.even_mul.
  - intros H. eapply Forall_forall in H.
    2: eapply list_max_le with (n := list_max l); lia.
    cbn in H. lia.
Qed.

Lemma generative_odd :
  generative (fun n : nat => Nat.odd n = true).
Proof.
  intros l. exists (1 + 2 * S (list_max l)). split.
  - now rewrite Nat.odd_succ, Nat.even_mul. 
  - intros H. eapply Forall_forall in H.
    2: eapply list_max_le with (n := list_max l); lia.
    cbn in H. lia.
Qed.

Definition P_inf P := (fun n => if Nat.even n then P else ~ P).

Lemma P_inf_spec P : 
  P \/ ~ P <->  exists n, P_inf P n.
Proof.
  split.
  - intros [H | H].
    + now exists 0.
    + now exists 1.
  - intros [n H]. red in H. destruct Nat.even; firstorder.
Qed.  



Lemma P_inf_non_finite P :
  ~ finite (P_inf P).
Proof.
  intros H. ccase P as [HP | HP].
  - eapply generative_non_exhaustible; eauto.
    eapply generative_ext. 2: eapply generative_even.
    intros n. unfold P_inf. destruct (Nat.even n); firstorder congruence.
  - eapply generative_non_exhaustible; eauto.
    eapply generative_ext. 2:eapply generative_odd.
    intros n. rewrite <- Nat.negb_even. unfold P_inf.
    destruct (Nat.even n); cbn; firstorder congruence.
Qed.
 *)

Lemma unbounded_inhabited {X} (p : X -> Prop) :
  unbounded p -> exists x, p x.
Proof.
  intros ([ | x [] ] & ? & ? & ?) % (fun H => H 1); cbn in *; try congruence.
  exists x. eauto.
Qed.

Lemma generative_full : generative (fun n : nat => True).
Proof.
  intros l. exists (list_max l + 1). split. eauto.
  intros H. eapply Forall_forall in H.
  2: eapply list_max_le with (n := list_max l); lia.
  cbn in H. lia.
Qed.

Lemma non_finite_unbounded_DNE :
  (forall (p : nat -> Prop), ~ exhaustible p -> unbounded p) -> DNE.
Proof.
  intros H P HP.
  unshelve epose proof (unbounded_inhabited (fun _ : nat => P) _) as []; [ | eassumption].
  eapply H. intros Hf. ccase P as [H1 | H1]; try tauto.
  eapply generative_non_exhaustible. 2: exact Hf.
  eapply generative_ext. 
  2: eapply generative_full.
  firstorder.
Qed.

Lemma non_finite_generative_DNE :
  (forall (p : nat -> Prop), ~ exhaustible p -> generative p) -> DNE.
Proof.
  intros H P. eapply non_finite_unbounded_DNE. intros p H0.
  apply generative_unbounded, H, H0.
Qed. 

Lemma non_finite_unbounded_LEM_iff :
  (forall X (p : X -> Prop), ~ exhaustible p -> unbounded p) <-> LEM.
Proof.
  split.
  - intros H. apply LEM_DNE, non_finite_unbounded_DNE, H.
  - intros. apply generative_unbounded. eapply non_exhaustible_generative; eauto.
Qed.

Lemma non_exhaustible_generative_LEM_iff :
  (forall X (p : X -> Prop), ~ exhaustible p -> generative p) <-> LEM.
Proof.
  split.
  - intros H. apply LEM_DNE, non_finite_unbounded_DNE. intros p H0. eapply generative_unbounded, H, H0.
  - intros. apply non_exhaustible_generative; eauto.
Qed.

Definition dedekind_infinite {X} (p : X -> Prop) := 
  exists f : nat -> X, forall n1, p (f n1) /\ forall n2, f n1 = f n2 -> n1 = n2.

Lemma map_NoDup {X Y} (f : X -> Y) l : (forall x1 x2, f x1 = f x2 -> x1 = x2) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hinj Hl. induction Hl; cbn; econstructor; eauto.
  now intros (? & <- % Hinj & ?) % in_map_iff.
Qed.

Lemma dedekind_infinite_unbounded {X} (p : X -> Prop) :
  dedekind_infinite p -> unbounded p.
Proof.
  intros [f Hf] n. exists (map f (seq 0 n)). repeat split.
  - now rewrite map_length, seq_length.
  - eapply map_NoDup. firstorder. eapply seq_NoDup.
  - intros x (? & <- & ?) % in_map_iff. eapply Hf.
Qed.

Fixpoint generate {X} (f : list X -> X) n := match n with 0 => [] | S n => generate f n ++ [f (generate f n)] end.

Lemma generative_is_prefix {X} (f : list X -> X) n1 n2 x :
  n1 <= n2 -> In x (generate f n1) -> In x (generate f n2).
Proof.
  induction 1 in x |- *.
  - eauto.
  - cbn. intros ? % IHle. eauto.
Qed.

Require Import stdpp.list.

Lemma generate_prefix {X} (f : list X -> X) n1 n2 : 
  n1 < n2 -> List.In (f (generate f n1)) (generate f n2).
Proof.  
  induction 1; cbn; eauto.
Qed.

Lemma weakly_generative_dedekind_infinite  {X} (p : X -> Prop) :
  inhabited (forall l, ∑ x, (forall x, In x l -> p x) -> ~ In x l /\ p x) ->
  dedekind_infinite p.
Proof.
  intros [F].
  pose (f x := proj1_sig (F x)).
  exists (fun n => f (generate f n)).
  assert (Hs : forall n x, In x (generate f n) -> p x). {
    induction n; intros x H; cbn in *.
    - firstorder.
    - eapply in_app_iff in H as [H | [<- | []]]. eauto.
      eapply (proj2_sig (F (generate f n))). eauto.
  }
  intros n1. split.
  + eapply (proj2_sig (F (generate f n1))). eapply Hs.
  + revert n1. enough (forall n1 n2, n1 < n2 -> f (generate f n1) <> f (generate f n2)) as HH.
    * intros n1 n2. assert (n1 < n2 \/ n1 = n2 \/ n1 > n2) as [H| [H|H]] by lia; firstorder congruence.
    * intros n1 n2 H % (generate_prefix f) He. rewrite He in *. clear He. unfold f in *.
      destruct F; cbn in *. firstorder.
Qed.

Lemma dedekind_infinite_spec {X} (p : X -> Prop) (Hd : forall x1 x2 : X, dec (x1 <> x2)) :
  dedekind_infinite p <-> inhabited (forall l, ∑ x, ~ In x l /\ p x).
Proof.
  split.
  - intros [f Hf]. econstructor. intros l.
    edestruct (pigeonhole_Sigma (map f (seq 0 (1 + length l))) l Hd) as (x & H1 & H2).
    + eapply map_NoDup. firstorder. eapply seq_NoDup.
    + rewrite map_length, seq_length. lia.
    + exists x. eapply in_map_iff in H1 as (? & <- & ?). firstorder.
  - intros [F]. eapply weakly_generative_dedekind_infinite.
    econstructor. intros l.
    destruct (F l) as [x]. exists x. eauto.
Qed.

Lemma dedekind_infinite_nat (p : nat -> Prop) :
  dedekind_infinite p <-> inhabited (forall n, ∑ m, m >= n /\ p m).
Proof.
  rewrite dedekind_infinite_spec. 2: exact _.
  split.
  - intros [H]. econstructor. intros n. specialize (H (seq 0 n)) as (x & H1 & H2).
    exists x. split; eauto.
    assert (x >= n \/ x < n) as [H | H] by lia; eauto.
    destruct H1. eapply in_seq. lia.
  - intros [H]. econstructor. intros l. specialize (H (1 + list_max l)) as (m & H1 & H2).
    exists m. split; eauto.
    assert (list_max l <= list_max l) as ? % list_max_le by lia.
    rewrite Forall_forall in H0.
    intros ? % elem_of_list_In % H0. lia.
Qed. 

Lemma dedekind_infinite_problem {X} (p : X -> Prop) :
  dedekind_infinite p -> exists q, enumerable q /\ dedekind_infinite q /\ forall x, q x -> p x.
Proof.
  intros [f Hf]. exists (fun x => exists n, f n = x). split. 2:split.
  - exists (fun n => Some (f n)). red. intros x; split; intros [n H]; exists n; congruence.
  - exists f. firstorder. eauto.
  - intros x [n <-]. apply Hf.
Qed.


(* Notation "'AC!!_nat' X"  := (forall R : nat -> X -> Prop, (forall n1 n2 x, R n1 x -> R n2 x -> n1 = n2) ->  (forall n, exists x, R n x) -> exists f : nat -> X, forall n, R n (f n)) (at level 10).

Lemma lt_list' {X} n (P : X -> nat -> Prop) k :
(forall m, m < n -> exists x, P x (k + m)) -> exists l, Forall2 P l (seq k n).
Proof.
intros H. induction n in k, H |- *; cbn.
- exists []. econstructor.
- edestruct (IHn (S k)) as [l IH].
  + intros. destruct (H (S m)) as [x Hx]. lia. exists x. now assert (S k + m = k + S m) as -> by lia. 
  + destruct (H 0 ltac:(lia)) as [x Hx]. exists (x :: l). econstructor. replace k with (k + 0) by lia. eauto. eauto.
Qed.

Lemma lt_list {X} n (P : X -> nat -> Prop) :
(forall m, m < n -> exists x, P x m) -> exists l, Forall2 P l (seq 0 n).
Proof.
intros H. apply lt_list'. cbn. eassumption.
Qed. *)
(* 
Require Import stdpp.list.

Lemma Forall2_in_l_r {X} {Y} R l1 l2 x :
  @Forall2 X Y R l1 l2 -> In x l1 -> exists y, R x y /\ In y l2.
Proof.
  induction 1.
  - inversion 1.
  - inversion 1; subst.
    + eauto.
    + eapply IHForall2 in H2 as (? & ? & ?); eauto.
Qed. *)

(* 
require import undecidability.shared.embed_nat.
import embednatnotations.

lemma generative_dedekind_infinite_ac :
  (forall (p : nat -> prop), unbounded p -> dedekind_infinite p) -> ac!!_nat nat.
proof.
  intros h r hinj htot.
  unshelve epose proof (h (fun! ⟨n,m⟩ => r n m) _) as [f hf].
  - intros n. unshelve epose proof (lt_list n (fun x n => r n x) _) as [l hl].
    1: now firstorder.
    exists l. repeat split.
    + eapply forall2_length_r. eassumption. now rewrite seq_length.
    + revert hl. generalize 0 as m. intros m hl. 
      induction l in m, n, hl |- *.
      * econstructor.
      * destruct n; inversion hl; subst; clear hl.
        econstructor.
        -- intros h7. destruct (forall2_in_l_r _ _ _ _ h5 h7) as (? & ? & [] % in_seq).
           specialize (hinj _ _ _ h0 h3) as ->. lia.
        -- eapply ihl; eapply h5.
    + intros ? h0. destruct (forall2_in_l_r _ _ _ _ hl h0) as (? & ? & ?). admit.
  - exists f. intros n. specialize (hf ⟨n,f n⟩) as [h1 h2]. rewrite embedp in h1.
qed.
*)
