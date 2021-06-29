From Computability Require Import Synthetic.DecidabilityFacts Synthetic.EnumerabilityFacts Synthetic.SemiDecidabilityFacts reductions partial embed_nat.
Require Import Setoid Program Lia.

Lemma sec_enum (p : nat -> Prop) : semi_decidable p <-> enumerable p.
Proof.
  split.
  - intros. eapply semi_decidable_enumerable; eauto.
  - intros. eapply enumerable_semi_decidable; eauto.
    eapply discrete_iff. econstructor. exact _.
Qed.

(** * Axioms for synthetic computability *)

(** ** Synthetic Church's thesis *)

Definition SCT :=
  exists T : nat -> nat -> nat -> option nat,
    (forall c x, monotonic (T c x)) /\
    forall f, exists c, forall x, exists n, T c x n = Some (f x).

Tactic Notation "intros" "⟨" ident(x) "," ident(n) "⟩" :=
  let xn := fresh "xn" in
  intros xn; destruct (unembed xn) as [x n]; rewrite (@embedP (x,n)).

Module halting_SCT.

  Variable T : nat -> nat -> nat -> option nat.
  Variable T_mono : forall c x, monotonic (T c x).

  Variable SCT : forall f, exists c, forall x, exists n, T c x n = Some (f x).

  Definition W c x := exists n v, T c x n = Some v.
  Definition K0 c := W c c.

  Lemma W_enumerable : enumerable (uncurry W).
  Proof.
    exists (fun! ⟨cx, n⟩ => (fun! ⟨c,x⟩ => if T c x n is Some v then Some (c,x) else None) cx).
    intros (c, x). cbn. split.
    - intros (n & v & H). exists ⟨⟨c,x⟩, n⟩. now rewrite !embedP, H.
    - intros [xnc H]. destruct (unembed xnc) as [cx n].
      destruct (unembed cx) as [c' x']. red. 
      destruct T eqn:E; inv H. eauto.
  Qed.

  Variable S11 : nat -> nat -> nat.

  Variable S11_assm : forall c x y v, (exists n, T c ⟨x, y⟩ n = Some v) <-> (exists n, T (S11 c x) y n = Some v).

End halting_SCT.

Record model_of_computation :=
  {
    T :> nat -> nat -> nat -> option nat ;
    T_mono : forall c x, monotonic (T c x) ;
    computes c f := forall x, exists n, T c x n = Some (f x)
  }.

Hint Resolve T_mono : core.

Definition CT (T : model_of_computation) := forall f, exists c, forall x, exists n, T c x n = Some (f x).

(** ** Enumerability Axiom  *)

Definition EA := exists e : nat -> (nat -> option nat),
    forall p, enumerable p -> exists c, enumerator (e c) p.

Definition φ (T : model_of_computation) c := fun! ⟨ n, m ⟩ => match T c n m with Some (S x) => Some x | _ => None end.

Lemma CT_to_EA' {T : model_of_computation} :
  CT T -> forall p, enumerable p -> exists c : nat, enumerator (φ T c) p.
Proof.
  intros ct p [f Hf].
  destruct (ct (fun n => match f n with Some x => S x | None => 0 end)) as [c Hc].
  exists c. intros x. rewrite (Hf x). unfold φ. symmetry.
  split.
  - intros [n Hn].
    destruct (unembed n) as (n1, n2).
    destruct (T c n1 n2) as [ [ | ] | ] eqn:E; inv Hn.
    exists n1. destruct (Hc n1).
    pose proof (monotonic_agnostic (T_mono T c n1) H E).
    destruct (f n1); congruence.
  - intros [n Hn].
    destruct (Hc n) as [m Hm].
    exists ⟨n,m⟩. now rewrite embedP, Hm, Hn.
Qed.

Lemma CT_to_EA {T : model_of_computation} :
  CT T -> EA.
Proof.
  intros ct. exists (φ T). now eapply CT_to_EA'.
Qed.

Definition EA' := exists e : nat -> (nat -> Prop), forall p : nat -> Prop, enumerable p <-> exists c, e c ≡{nat -> Prop} p.

Lemma EA_to_EA'  : 
  EA -> EA'.
Proof.
  intros [φ H].
  exists (fun c x => exists n, φ c n = Some x). intros p.
  split.
  - intros [c Hc] % H. exists c. cbn. firstorder.
  - intros [c Hc]. exists (φ c). firstorder.
Qed.

(** ** Enumerability of Partial Functions  *)

Instance equiv_part `{partiality} {A} : equiv_on (part A) := {| equiv_rel := @partial.equiv _ A |}.

Definition EPF {Part : partiality} := exists e : nat -> (nat ↛ nat), forall f : nat ↛ nat, exists n, e n ≡{nat ↛ nat} f.

Definition e `{partiality} {T : model_of_computation} := (fun c x => mkpart (fun arg => let (n, m) := unembed arg in match T c ⟨ x, n ⟩ m with Some (S x) => Some x | _ => None end)).

Definition toenum `{partiality} (f : nat ↛ nat) (n : nat) :=
  let (x,n) := unembed n in
  match seval (f x) n with Some y => Some (x,y) | None => None end.

Definition ofenum `{partiality} (g : nat -> option (nat * nat)) (x : nat) :=
  bind (mu_tot (fun n => match g n with Some (x', y) => Nat.eqb x x' | _ => false end))
       (fun n => match g n with Some (_, y) => ret y | _ => undef end).

Lemma toenum_spec {Part : partiality} (f : nat ↛ nat) x y :
  (f x =! y) <-> (exists n, toenum f n = Some (x,y)).
Proof.
  unfold toenum. split.
  - intros H.
    eapply seval_hasvalue in H as [n H].
    exists (⟨ x, n ⟩). now rewrite embedP, H.
  - intros [n H].
    destruct (unembed n), seval eqn:E; inv H.
    eapply seval_hasvalue. eauto.
Qed.

Lemma ofenum_ter_iff {Part : partiality} g x :
  (ter (ofenum g x)) <-> (exists n y, g n = Some (x, y)).
Proof.
  unfold ofenum. split.
  - intros [y H].
    eapply bind_hasvalue in H as [n [[H1 H2] % mu_tot_hasvalue H3]].
    destruct (g n) as [[x' y']|] eqn:E.
    + eapply ret_hasvalue_inv in H3.
      exists n, y.
      destruct (PeanoNat.Nat.eqb_spec x x').
      all:congruence.
    + now eapply undef_hasvalue in H3.
  - intros [n (_ & [y H] & Hleast)] % mu_nat_dep_least.
    + exists y.
      rewrite bind_hasvalue.
      exists n. rewrite mu_tot_hasvalue, H.
      rewrite NPeano.Nat.eqb_refl.
      repeat split. 2:eapply ret_hasvalue.
      intros. destruct (g m) as [ [x' y'] | ] eqn:E.
      * eapply NPeano.Nat.eqb_neq.
        intros ->.
        enough (n <= m) by lia. eapply Hleast.
        lia. eauto.
      * reflexivity.
    + intros n.
      destruct (g n) as [ [x' ] | ]; try firstorder congruence.
      destruct (Dec.nat_eq_dec x x'); subst; eauto; firstorder congruence.
Qed.

Lemma ofenum_spec {Part : partiality} (g : nat -> option (nat * nat)) x y :
  ofenum g x =! y -> (exists n, g n = Some (x,y)).
Proof.
  unfold ofenum.
  intros H. eapply bind_hasvalue in H as [n [[H1 _] % mu_tot_hasvalue H2]].
  destruct (g n) as [[x' y']|] eqn:E.
  + eapply ret_hasvalue_inv in H2. subst.
    eapply EqNat.beq_nat_true in H1 as ->. eauto.
  + now eapply undef_hasvalue in H2.
Qed.

(* Lemma ofenum_ter {Part : partiality} (g : nat -> option (nat * nat)) n x y : *)
(*   g n = Some (x,y) -> ter (ofenum g x). *)
(* Proof. *)
(*   intros H. eapply ofenum_ter_iff. eauto. *)
(* Qed. *)

Lemma enumerator_graph {Part : partiality} :
  forall f : nat ↛ nat, enumerator (fun! ⟨x,n⟩ => if seval (f x) n is Some fx then
                                   Some ⟨x, fx⟩ else None ) (fun! ⟨x,fx⟩  => f x =! fx).
Proof.
  intros f xfx. destruct (unembed xfx) as [x fx] eqn:E. split.
  - intros [n H] % seval_hasvalue.
    exists ⟨x,n⟩. rewrite embedP, H. f_equal.
    symmetry. now rewrite <- unembedP, E.
  - intros [xn Hn]. destruct (unembed xn) as [x' n].
    eapply seval_hasvalue. destruct seval eqn:Ee; inv Hn.
    rewrite embedP in E. inv E. eauto.
Qed.

Theorem EA_to_EPF {Part : partiality} :
  EA -> EPF.
Proof.
  intros [e EA].
  exists (fun c => ofenum (fun n => match e c n with Some n => Some (unembed n) | None => None end)).
  intros f.
  destruct (EA (fun! ⟨n, m⟩ => f n =! m)) as [c Hc].
  { eexists. eapply enumerator_graph. }
  exists c. intros x y.
  pose proof (Hc ⟨x,y⟩) as Hc'. cbn in Hc'. rewrite embedP in Hc'.
  rewrite Hc'.
  split.
  - intros [n H] % ofenum_spec.
    destruct (e c n) as [xy|] eqn:E ; inv H.
    exists n. now rewrite unembedP.
  - intros H.
    unfold ofenum.
    eapply mu_nat_dep_least in H as (n & _ & H & Hl).
    2:{ intros n. clear. destruct (e c n); try firstorder congruence.
        destruct (Dec.nat_eq_dec n0 ⟨x,y⟩); firstorder congruence. }
    eapply bind_hasvalue. exists n. split.
    + eapply mu_tot_hasvalue. split.
      rewrite H, embedP. eapply PeanoNat.Nat.eqb_refl.
      intros. destruct (e c m) eqn:E2.
      * destruct unembed eqn:E. destruct (PeanoNat.Nat.eqb_spec x n1); try congruence.
        subst. eapply (f_equal embed) in E. rewrite unembedP in E. subst.
        enough (y = n2) as ->.
        -- eapply Hl in E2; lia. 
        -- eapply hasvalue_det. eapply Hc'. eauto.
           specialize (Hc ⟨n1, n2⟩). cbn in Hc. rewrite embedP in Hc.
           eapply Hc. eauto.
      * reflexivity.
    + rewrite H, embedP. eapply ret_hasvalue.
Qed.

Theorem EPF_to_EA {Part : partiality} :
  EPF -> EA.
Proof.
  intros [e EPF].
  exists (fun c n => match toenum (e c) n with Some (x,y) => Some x | _ => None end).
  intros p [f Hf].
  pose (f' := (fun n => match f n with Some x => Some (x,x) | _ => None end)).
  destruct (EPF (ofenum f')) as [c Hc].
  exists c. intros x. rewrite (Hf x). symmetry.
  transitivity (exists y, e c x =! y). {
    split.
    - intros [n H].
      destruct toenum as [[m1 y]|] eqn:E; inv H.
      exists y. eapply toenum_spec. eauto.
    - intros [y Hy].
      eapply toenum_spec in Hy as [n Hn].
      exists n. now rewrite Hn.
  }
  transitivity (exists y, ofenum f' x =! y).
  - split; intros [y Hy]; exists y; now eapply Hc.
  - transitivity (ter (ofenum f' x)). reflexivity.
    rewrite ofenum_ter_iff. unfold f'.
    split.
    + intros [n [y H]]. exists n. destruct (f n); congruence.
    + intros [n H]. exists n, x.
      now rewrite H.
Qed.

(** ** Synthetic Church's thesis for partial functions  *)

Definition CTP `{partiality} := exists T : nat -> nat -> nat -> option nat,
    (forall c x, monotonic (T c x)) /\ forall f : nat ↛ nat, exists c, forall x y, f x =! y <-> exists n, T c x n = Some y.

Lemma EPF_to_CTP `{partiality} :
  EPF -> CTP.
Proof.
  intros [e EPF].
  unshelve eexists. 2: split.
  - exact (fun c x n => seval (e c x) n).
  - cbn. intros c x y n1 Hn1 n2 len.
    eapply seval_mono; eauto.
  - intros f.
    destruct (EPF f) as [c Hc].
    exists c. intros x y.
    cbn. specialize (Hc x). cbn in Hc. red in Hc.
    setoid_rewrite <- Hc.
    eapply seval_hasvalue.
Qed.

Lemma CTP_to_CT `{partiality} :
  CTP -> SCT.
Proof.
  intros (T & T_mono & CTP). exists T. split; eauto.
  intros f. destruct (CTP (fun x => ret (f x))) as [n Hn].
  exists n. intros x.
  eapply Hn, ret_hasvalue.
Qed.

Section Cantor.

  Variable A : Type.
  Variable g : A -> (A -> Prop).

  Lemma Cantor : surjection_wrt ext_equiv g -> False.
  Proof.
    intros g_surj.
    pose (h x1 := ~ (g x1 x1)).
    destruct (g_surj h) as [n H].
    firstorder.
  Qed.

End Cantor.

(* Lemma partial_to_total `{Part : partiality} (f : nat ↛ nat) : *)
(*   {f' : nat -> nat | forall x a, f x =! a <-> exists n, f' ⟨x, n⟩ = S a }. *)
(* Proof. *)
(*   exists (fun arg => let (x,n) := unembed arg in match seval (f x) n with Some a => S a | None => 0 end). *)
(*   move => x a. split. *)
(*   - move => / seval_hasvalue [n H]. *)
(*     exists n. now rewrite embedP H. *)
(*   - move => [n H]. rewrite embedP in H. *)
(*     eapply seval_hasvalue. exists n. *)
(*     destruct seval; congruence. *)
(* Qed. *)

Definition EPF_bool `{partiality} := exists e : nat -> (nat ↛ bool), forall f : nat ↛ bool, exists n, e n ≡{nat ↛ bool} f.

Section assm_part.

Context {Part : partiality}.

Let F (g : nat ↛ nat) x := bind (g x) (fun y => if Nat.eqb y 0 then ret true else ret false).
Let G (f : nat ↛ bool) x := bind (f x) (fun y => if y then ret 0 else ret 1).

Lemma EPF_to_EPF_bool  :
  EPF -> EPF_bool.
Proof.
  intros [e H].
  exists (fun n => F (e n)).
  intros f. destruct (H (G f)) as [c Hc].
  exists c. intros x y. unfold F.
  rewrite bind_hasvalue. cbn in Hc. unfold partial.equiv in Hc.
  setoid_rewrite Hc.
  split.
  - intros [a [H1 H2]].
    destruct (PeanoNat.Nat.eqb_spec a 0); subst.
    + eapply ret_hasvalue_inv in H2. subst.
      unfold G in H1. eapply bind_hasvalue in H1 as [[] [H1 H2]].
      * eauto.
      * eapply ret_hasvalue_inv in H2; congruence.
    + eapply ret_hasvalue_inv in H2. subst.
      unfold G in H1. eapply bind_hasvalue in H1 as [[] [H1 H2]].
      * eapply ret_hasvalue_inv in H2; congruence.
      * eauto.
  - intros H1.
    exists (if y then 0 else 1). split.
    + unfold G. rewrite bind_hasvalue. exists y; split; eauto. destruct y; eapply ret_hasvalue.
    + destruct y; eapply ret_hasvalue.
Qed.

End assm_part.

(** ** SMN and composition  *)

Definition SMN_for (T : nat -> nat -> nat -> option nat) :=
  (exists S : nat -> nat -> nat, forall c x y v, (exists n, T c ⟨x,y⟩ n = Some v) <-> (exists n, T (S c x) y n = Some v)).

Definition SCTS_star :=
  exists T : nat -> nat -> nat -> option nat,
    (forall c x, monotonic (T c x)) /\
    (forall f, exists c, forall x, exists n, T c x n = Some (f x)) /\
  SMN_for T.

Definition SMN (φ : nat -> nat -> option nat) :=
  let W c x := exists n, φ c n = Some x in                      (* This is SMN *)
  exists s, forall c x y, W (s c x) y <-> W c ⟨x,y⟩.

Definition EAS_star :=
  exists φ : nat -> (nat -> option nat),
    (forall p, enumerable p -> exists c, enumerator (φ c) p) /\ SMN φ.

Definition SCTS :=
  exists T : nat -> nat -> nat -> option nat,
    (forall c x, monotonic (T c x)) /\
    (forall f : nat -> nat -> nat, exists c : nat -> nat, forall x y, exists n, T (c x) y n = Some (f x y)).

Definition EAP :=
  exists φ, forall p : nat -> nat -> Prop, penumerable p ->
                         exists c : nat -> nat, forall x, enumerator (φ (c x)) (p x).

Definition EAS :=
  exists φ, forall p : nat -> nat -> Prop, enumerable (fun! ⟨x,y⟩ => p x y) ->
                         exists c : nat -> nat, forall x, enumerator (φ (c x)) (p x).

Lemma SCTS_star_to_SCTS :
  SCTS_star -> SCTS. 
Proof.
  intros (T & Tmono & HT & S & HS).
  exists T. split.
  - eapply Tmono.
  - intros f.
    destruct (HT (fun! ⟨x,y⟩ => f x y)) as [c0 Hc0].
    exists (S c0). intros.
    eapply HS. edestruct (Hc0 ⟨x,y⟩). rewrite embedP in H. 
    eauto.
Qed.

Definition EAS' :=
  exists φ, forall p : nat -> nat -> Prop, enumerable (uncurry p) ->
                         exists c : nat -> nat, forall x, enumerator (φ (c x)) (p x).

Lemma EAS_to_EAP :
  EAS' -> EAP.
Proof.
  intros [φ Hφ].
  exists φ. intros p H % penumerable_iff; eauto. eapply discrete_nat.
Qed.

Lemma EAP_to_EAS :
  EAP -> EAS'.
Proof.
  intros [φ Hφ].
  exists φ. intros p H % penumerable_iff; eauto. eapply discrete_nat.
Qed.

Lemma SCTS_to_EAS :
  SCTS -> EAS'.
Proof.
  intros (T & Tmono & HT).
  unshelve eexists (φ _).
  eexists. 
  - eauto.
  - intros p [f Hf]. unfold φ. cbn.
    specialize (HT (fun x n => if f n is Some (x',y) then if Nat.eqb x' x then S y else 0 else 0)) as [c Hc].
    exists c. intros x y. split.
    + intros H. eapply (Hf (x,y)) in H as [n H].
      destruct (Hc x n) as [m Hm].
      exists ⟨n,m⟩. now rewrite embedP, Hm, H, PeanoNat.Nat.eqb_refl.
    + intros [nm H]. destruct (unembed nm) as [n m].
      destruct T eqn:E; try congruence.
      destruct n0; inv H.
      specialize (Hc x n) as [m' H'].
      unshelve epose proof (monotonic_agnostic _ E H'). eauto.
      destruct (f n) as [[x' y']| ] eqn:E'; try congruence.
      destruct (PeanoNat.Nat.eqb_spec x' x); inv H.
      eapply (Hf (x,y')). eauto.
Qed.

Lemma SCTS_to_EAP :
  SCTS -> EAP.
Proof.
  intros (T & Tmono & HT).
  unshelve eexists (φ _).
  eexists. 
  - eauto.
  - intros p [f Hf]. unfold φ. cbn.
    specialize (HT (fun x n => if f x n is Some y then S y else 0)) as [c Hc].
    exists c. intros x y. split.
    + intros H. eapply (Hf x y) in H as [n H].
      destruct (Hc x n) as [m Hm].
      exists ⟨n,m⟩. now rewrite embedP, Hm, H.
    + intros [nm H]. destruct (unembed nm) as [n m].
      destruct T eqn:E; try congruence.
      destruct n0; inv H.
      specialize (Hc x n) as [m' H'].
      unshelve epose proof (monotonic_agnostic _ E H'). eauto.
      destruct (f x n) as [y'| ] eqn:E'; try congruence. inv H.
      eapply Hf. eauto.
Qed.

Lemma SCTS_to_EAS' :
  SCTS -> EAS.
Proof.
  intros (T & Tmono & HT).
  unshelve eexists (φ _).
  eexists. 
  - eauto.
  - intros p [f Hf]. unfold φ. cbn.
    specialize (HT (fun x n => if f n is Some xy then (fun! ⟨x',y⟩ => if Nat.eqb x' x then S y else 0) xy else 0)) as [c Hc].
    exists c. intros x y. split.
    + intros H. specialize (Hf ⟨x,y⟩). cbn in Hf. rewrite embedP in Hf.
      eapply Hf in H as [n H].
      destruct (Hc x n) as [m Hm].
      exists ⟨n,m⟩. now rewrite embedP, Hm, H, embedP, PeanoNat.Nat.eqb_refl.
    + intros [nm H]. destruct (unembed nm) as [n m].
      destruct T eqn:E; try congruence.
      destruct n0; inv H.
      specialize (Hc x n) as [m' H'].
      unshelve epose proof (monotonic_agnostic _ E H'). eauto.
      destruct (f n) eqn:E'; try congruence.
      destruct (unembed n0) as [n1 y'] eqn:E0.
      destruct (PeanoNat.Nat.eqb_spec n1 x); inv H.
      specialize (Hf ⟨x,y'⟩). cbn in Hf. rewrite embedP in Hf. eapply Hf.
      exists n. eapply (f_equal embed) in E0. rewrite unembedP in E0.
      congruence.
Qed. 

Lemma EAS_EAS_star :
  EAS' -> EAS_star.
Proof.
  intros (φ & H).
  assert (lem : forall p : nat -> Prop, enumerable p -> exists c : nat, enumerator (φ c) p). { 
    intros p [f Hf]. destruct (H (fun _ => p)) as [c0 Hc0].
    + exists (fun! ⟨x,n⟩ => if f n is Some y then Some (x,y) else None).
      intros [x y]. 
      rewrite (Hf y). 
      split.
      * intros [n Hn]. exists ⟨x,n⟩. now rewrite embedP, Hn. 
      * intros [xn Hn]. destruct (unembed xn) as [x' n].
        destruct f eqn:E'; inv Hn. eauto. 
    + exists (c0 0). eauto.
  }
  exists φ. split.
  - eapply lem.
  - cbn. destruct (H (fun! ⟨c,x⟩ => fun y => exists n, φ c n = Some ⟨x,y⟩)) as [γ Hγ].
    + eexists (fun! ⟨c,n⟩ => if φ c n is Some xy then (fun! ⟨x,y⟩ => Some (⟨c,x⟩, y)) xy else @None _). intros [cx y].
      destruct (unembed cx) as [c x] eqn:E'.
      eapply (f_equal embed) in E'. rewrite unembedP in E'.
      subst. split.
      * cbn. rewrite embedP. intros [n Hn]. exists ⟨c,n⟩.
        now rewrite embedP, Hn, embedP.
      * intros [n Hn]. destruct (unembed n) as [c' n'].
        destruct φ eqn:E; try congruence.
        destruct (unembed n0) as [x' y'] eqn:E'. inv Hn.
        eapply (f_equal unembed) in H1. rewrite !embedP in H1.
        inv H1.
        eapply (f_equal embed) in E'. rewrite !unembedP in E'. subst.
        cbn. rewrite embedP. eauto.
    + exists (fun c x => γ ⟨c,x⟩). unfold enumerator in Hγ.
      intros. specialize (Hγ ⟨c,x⟩ y). rewrite embedP in Hγ.
      symmetry. eassumption.
Qed.

Lemma EAS_EAS_star' :
  EAS -> EAS_star.
Proof.
  intros (φ & H).
  assert (lem : forall p : nat -> Prop, enumerable p -> exists c : nat, enumerator (φ c) p). { 
    intros p [f Hf]. destruct (H (fun _ => p)) as [c0 Hc0].
    + exists (fun! ⟨x,n⟩ => if f n is Some y then Some ⟨x,y⟩ else None).
      intros xy. destruct (unembed xy) as [x y] eqn:E.
      rewrite (Hf y). 
      split.
      * intros [n Hn]. exists ⟨x,n⟩. rewrite embedP, Hn.
        eapply (f_equal embed) in E. rewrite unembedP in E. congruence.
      * intros [xn Hn]. destruct (unembed xn) as [x' n].
        destruct f eqn:E'; inv Hn. rewrite embedP in E.
        inv E. eauto.
    + exists (c0 0). eauto.
  }
  exists φ. split.
  - eapply lem.
  - cbn. destruct (H (fun! ⟨c,x⟩ => fun y => exists n, φ c n = Some ⟨x,y⟩)) as [γ Hγ].
    + eexists (fun! ⟨c,n⟩ => if φ c n is Some xy then (fun! ⟨x,y⟩ => Some ⟨⟨c,x⟩, y⟩) xy else @None nat). intros cxy.
      destruct (unembed cxy) as [cx y] eqn:E.
      eapply (f_equal embed) in E. rewrite unembedP in E.
      destruct (unembed cx) as [c x] eqn:E'.
      eapply (f_equal embed) in E'. rewrite unembedP in E'.
      subst. split.
      * intros [n Hn]. exists ⟨c,n⟩.
        now rewrite embedP, Hn, embedP.
      * intros [n Hn]. destruct (unembed n) as [c' n'].
        destruct φ eqn:E; try congruence.
        destruct (unembed n0) as [x' y'] eqn:E'. inv Hn.
        eapply (f_equal unembed) in H1. rewrite !embedP in H1.
        inv H1.
        eapply (f_equal unembed) in H2. rewrite !embedP in H2. inv H2.
        eapply (f_equal embed) in E'. rewrite !unembedP in E'. subst.
        eauto.
    + exists (fun c x => γ ⟨c,x⟩). unfold enumerator in Hγ.
      intros. specialize (Hγ ⟨c,x⟩ y). rewrite embedP in Hγ.
      symmetry. eassumption.
Qed.

(* Lemma SCTS_to_EA_star : *)
(*   SCTS_star -> EAS_star. *)
(* Proof. *)
(*   intros (T & Tmono & HT & S & HS). *)
(*   eexists. split. *)
(*   - unshelve eapply CT_to_EA'. 1: now econstructor. now cbv.  *)
(*   - red. unfold φ. cbn. *)
(*     destruct (HT ((fun xx'v => (fun! ⟨x,x'v⟩ => if x'v is S x'v then (fun! ⟨x',v⟩ => if Nat.eqb x x' then 1 + v else 0) x'v else 0) xx'v)))  as [c0 Hc0]. *)
(*     exists (fun c x => C c (S c0 x)). *)
(*     intros. split. *)
(*     + intros [nm Hnm]. destruct (unembed nm) as [n m]. *)
(*       destruct T eqn:E; inv Hnm. *)
(*       destruct n0; inv H0. *)
(*       specialize (HC c (S c0 x) n (1 + y)) as [(k1 & y' & k2 & H1 & H2) _]; [ eauto | ]. *)
(*       exists ⟨n, k1⟩. rewrite embedP, H1. *)
(*       specialize (HS c0 x y' (1 + y)) as [_ [k H]]; [ eauto | ]. *)
(*       specialize (Hc0 ⟨x,y'⟩) as [k3 H3]. *)
(*       unshelve epose proof (monotonic_agnostic _ H H3); eauto. *)
(*       rewrite embedP in H0. *)
(*       destruct y'; try lia.  *)
(*       destruct (unembed y') eqn:EE. destruct (PeanoNat.Nat.eqb_spec x n0); try lia. *)
(*       subst. f_equal. eapply (f_equal embed) in EE. rewrite unembedP in EE. subst. *)
(*       cbn in *. congruence. *)
(*     + intros [nm Hnm]. destruct (unembed nm) as [n m]. *)
(*       destruct T eqn:E; inv Hnm. *)
(*       destruct n0; inv H0. *)
(*       specialize (Hc0 ( ⟨ x, Datatypes.S ⟨ x, y ⟩ ⟩)) as [k Hk]. *)
(*       specialize (HS c0 x (Datatypes.S ⟨ x, y ⟩)) as [[k2 H2] _]; [ eauto | ]. *)
(*       specialize (HC c (S c0 x) n) as [_ [k1 H1]]; [eauto | ]. *)
(*       eexists ⟨_,_⟩. now rewrite embedP, H1, !embedP, PeanoNat.Nat.eqb_refl. *)
(* Qed. *)

Require Import Computability.Synthetic.ReducibilityFacts.

Fixpoint mk_mono {X} (f : nat -> option X) (n : nat) : option X :=
  match n with
  | 0 => None
  | S n => if mk_mono f n is Some x then Some x else f n
  end.

Lemma monotonic_mk_mono {X} (f : nat -> option X) :
  monotonic (mk_mono f).
Proof.
  intros n1 v H1 n2 H2.
  induction H2; cbn; eauto.
  now rewrite IHle.
Qed.

Lemma mk_mono_spec {X} (f : nat -> option X) n x :
  mk_mono f n = Some x <-> exists m, m < n /\ f m = Some x /\ forall m', f m' <> None -> m <= m'.
Proof.
  revert x. pattern n. eapply Wf_nat.lt_wf_ind.
  clear. intros n IH x. destruct n; cbn.
  - clear IH. split.
    + firstorder. exists 0. firstorder congruence.
    + intros (m & H1 & H2 & H3). assert (m = 0) as -> by lia. lia.
  - destruct mk_mono eqn:E.
    + eapply IH in E as (m & H1 & H2 & H3); try lia.
      split.
      * intros [= ->]. exists m. split. lia. eauto.
      * intros (m' & H1' & H2' & H3').
        enough (m = m') by congruence.
        enough (m <= m' /\ m' <= m) by lia.
        split; [ eapply H3 | eapply H3']; congruence.
    + split.
      * intros H. exists n. repeat split; eauto.
        intros. enough (~ m' < n) by lia. intros ?.
        assert (exists m', f m' <> None). { eauto. }
        eapply mu_nat_dep_least in H2 as (l & _ & H4 & H5). 2: { intros k; destruct (f k); firstorder congruence. }
        destruct (f l) as [x' | ] eqn:E'; try congruence.
        enough (None = Some x') by congruence. rewrite <- E.
        eapply IH. lia. exists l. repeat eapply conj.
        -- enough (l <= m') by lia. eapply H5. lia. eauto.
        -- eauto.
        -- intros. eapply H5. lia. eauto.
      * intros (m & H1 & H2 & H3).
        assert (m = n \/ m < n) as [-> | ] by lia; eauto.
        enough (None = Some x) by congruence.
        rewrite <- E. eapply IH. lia.
        exists m. split. lia. eauto.
Qed.

Lemma EA_to_SCT :
  EA -> SCT.
Proof.
  intros [e EA].
  exists (fun c x => mk_mono (fun n => if e c n is Some xy then (fun! ⟨x',y⟩ => if Nat.eqb x x' then Some y else None) xy else None)).
  split. 1: intros; eapply monotonic_mk_mono.
  intros f.
  destruct (EA (fun! ⟨n, m⟩ => f n = m)) as [c Hc].
  { eapply enumerable_red. 4:eapply enumerable_graph.
    - exists (fun! ⟨n,m⟩ => (n,m)).
      intros nm. destruct (unembed nm) as [n m]. split.
      + intros H. exists n. f_equal. symmetry. exact H.
      + now intros [? [= -> ->]].
    - eauto.
    - eapply discrete_iff. eauto.
    - eauto.
  }
  exists c. intros x.
  pose proof (Hc ⟨x,f x⟩) as Hc'. cbn in Hc'. rewrite embedP in Hc'.
  destruct Hc' as [H _]. specialize (H eq_refl).
  unfold ofenum.
  eapply mu_nat_dep_least in H as (n & _ & H & Hl).
  2:{ intros n. clear. destruct (e c n); try firstorder congruence.
      destruct (Dec.nat_eq_dec n0 ⟨x,f x⟩); firstorder congruence. }

  exists (S n). eapply mk_mono_spec. exists n. repeat eapply conj.
  + lia.
  + now rewrite H, embedP, PeanoNat.Nat.eqb_refl.
  + intros. specialize (Hl m' ltac:(lia)). destruct (e c m') as [x'y | ] eqn:E; try congruence.
    destruct (unembed x'y) as [x' y] eqn:E'.
    eapply (f_equal embed) in E'. rewrite unembedP in E'. subst.
    assert (f x' = y). {
      specialize (Hc ⟨x', y⟩). cbn in Hc. rewrite embedP in Hc. eapply Hc.
      eauto.
    } 
    destruct (PeanoNat.Nat.eqb_spec x x'); try congruence.
    subst. eauto.
Qed.

Lemma EAS_to_SCT :
  EAS' -> SCTS.
Proof.
  intros [e EA].
  exists (fun c x => mk_mono (fun n => if e c n is Some xy then (fun! ⟨x',y⟩ => if Nat.eqb x x' then Some y else None) xy else None)).
  split. 1: intros; eapply monotonic_mk_mono.
  intros f.
  destruct (EA (fun x => fun! ⟨n, m⟩ => f x n = m)) as [c Hc].
  { eapply enumerable_red. 4:eapply enumerable_graph with (f0 := (fun '(x,n) => f x n)).
    - exists (fun '(x,nm) => (fun! ⟨n,m⟩ => ((x,n),m)) nm).
      intros [x nm]. cbn. 
      destruct (unembed nm) as [n m].
      split.
      + intros H. exists (x,n). f_equal. symmetry. exact H.
      + now intros [[] [= -> -> ->]].
    - eauto.
    - eapply discrete_iff. eauto.
    - eauto.
  }
  exists c. intros x y.
  pose proof (Hc x ⟨y,f x y⟩) as Hc'. cbn in Hc'. rewrite embedP in Hc'.
  destruct Hc' as [H _]. specialize (H eq_refl).
  unfold ofenum.
  eapply mu_nat_dep_least in H as (n & _ & H & Hl).
  2:{ intros n. clear. destruct (e (c x) n); try firstorder congruence.
      destruct (Dec.nat_eq_dec n0 ⟨y,f x y⟩); firstorder congruence. }

  exists (S n). eapply mk_mono_spec. exists n. repeat eapply conj.
  + lia.
  + now rewrite H, embedP, PeanoNat.Nat.eqb_refl.
  + intros. specialize (Hl m' ltac:(lia)). destruct (e (c x) m') as [x'y | ] eqn:E; try congruence.
    destruct (unembed x'y) as [x' y'] eqn:E'.
    eapply (f_equal embed) in E'. rewrite unembedP in E'. subst.
    assert (f x x' = y'). {
      specialize (Hc x ⟨x', y'⟩). cbn in Hc. rewrite embedP in Hc. eapply Hc.
      eauto.
    } 
    destruct (PeanoNat.Nat.eqb_spec y x'); try congruence.
    subst. eauto.
Qed.

Lemma EAS_to_SCTS' :
  EAS -> SCTS.
Proof.
  intros [e EA].
  exists (fun c x => implementation.the_fun (ofenum (H := implementation.monotonic_functions) (fun n => match e c n with Some n => Some (unembed n) | None => None end) x)).
  split. { intros. eapply implementation.spec_fun. } 
  intros f.
  destruct (EA (fun x => fun! ⟨n, m⟩ => f x n = m)) as [c Hc].
  { eapply enumerable_red. 4:eapply enumerable_graph with (f0 := (fun '(x,n) => f x n)).
    - exists (fun! ⟨x,nm⟩ => (fun! ⟨n,m⟩ => ((x,n),m)) nm).
      intros knm. destruct (unembed knm) as [k nm].
      destruct (unembed nm) as [n m].
      split.
      + intros H. exists (k,n). f_equal. symmetry. exact H.
      + now intros [[] [= -> -> ->]].
    - eauto.
    - eapply discrete_iff. eauto.
    - eauto.
  }
  exists c. intros x y.
  pose proof (Hc x ⟨y,f x y⟩) as Hc'. cbn in Hc'. rewrite embedP in Hc'.
  destruct Hc' as [H _]. specialize (H eq_refl).
  unfold ofenum.
  eapply mu_nat_dep_least in H as (n & _ & H & Hl).
  2:{ intros n. clear. destruct (e (c x) n); try firstorder congruence.
      destruct (Dec.nat_eq_dec n0 ⟨y,f x y⟩); firstorder congruence. }

  eapply (@bind_hasvalue implementation.monotonic_functions). exists n. split.
  + eapply mu_tot_hasvalue. split.
    rewrite H, embedP. eapply PeanoNat.Nat.eqb_refl.
    intros. destruct (e (c x) m) eqn:E2.
    * destruct unembed eqn:E. destruct (PeanoNat.Nat.eqb_spec y n1); try congruence.
      subst. eapply (f_equal embed) in E. rewrite unembedP in E. subst.
      enough (f x n1 = n2) as <-.
      -- eapply Hl in E2; lia. 
      -- specialize (Hc x ⟨n1, n2⟩). cbn in Hc. rewrite embedP in Hc.
         eapply Hc. eauto.
    * reflexivity.
  + rewrite H, embedP. eapply ret_hasvalue.
Qed.

(* Lemma SCTS_to_SCTS_star : *)
(*   SCTS -> SCTS_star. *)
(* Proof. *)
(*   intros (T & Hmono & HT). *)
(*   exists T. repeat eapply conj. *)
(*   - eauto. *)
(*   - intros f. destruct (HT (fun _ => f)) as [c Hc]. exists (c 0). intros. eapply (Hc 0). *)
(*   -  *)

Lemma EAS_star_to_EAS' :
  EAS_star -> EAS.
Proof.
  intros (φ & Hφ & S & HS).
  exists φ.
  intros p Hp.
  destruct (Hφ _ Hp) as [c Hc].
  exists (fun x => S c x). intros x y. red in Hc.
  now rewrite HS, <- Hc, embedP.
Qed.


Lemma enumerable_pair_red:
  forall p : nat -> nat -> Prop, enumerable (uncurry p) -> enumerable (fun! ⟨ x, y ⟩ => p x y).
Proof.
  intros p Hp.
  eapply enumerable_red; eauto. 2: eapply discrete_iff; eauto.
  exists unembed. intros xy.
  destruct (unembed xy) as [x y]. reflexivity.
Qed.

Lemma EAS_star_to_EAS :
  EAS_star -> EAS'.
Proof.
  intros (φ & Hφ & S & HS).
  exists φ.
  intros p Hp % enumerable_pair_red.

  destruct (Hφ _ Hp) as [c Hc].
  exists (fun x => S c x). intros x y. red in Hc.
  now rewrite HS, <- Hc, embedP.
Qed.

Definition SCT_bool :=
  exists ϕ : nat -> nat -> nat -> option bool,
    (forall c x, monotonic (ϕ c x)) /\
    forall f : nat -> nat -> bool, exists γ, forall x y,exists n,  ϕ (γ x) y n = Some (f x y).

Lemma SCT_to_SCT_bool :
  SCTS -> SCT_bool.
Proof.
  intros (ϕ & Hϕ & SCT).
  exists (fun c x n => if ϕ c x n is Some x then Some (Nat.eqb x 0) else None).
  split.
  - intros c x n1 v H n2 Hl.
    specialize (Hϕ c x n1).
    destruct (ϕ c x n1); inv H.
    now rewrite (Hϕ _ eq_refl _ Hl). 
  - intros f. destruct (SCT (fun x y => if f x y then 0 else 1)) as [γ Hγ].
    exists γ. intros x y. destruct (Hγ x y) as [n H].
    exists n. rewrite H. f_equal. destruct (f x y); reflexivity.
Qed.

Require Import List.
Import ListNotations.
Import implementation.

Definition I (f : nat -> nat) (n : nat) : bool :=
  nth n (flat_map (fun n => List.repeat false n ++ [true]) (map f (seq 0 (1 + n)))) false.

Fixpoint R (f : nat -> part bool) (x : nat) : part nat :=
  match x with
  | 0 => mu f
  | S x => bind (mu f) (fun n => R (fun m => f (m + S n)) x)
  end.

Lemma R_spec0:
  forall (g : nat ↛ bool) (f : nat -> nat),
    (forall x : nat, g x =! I f x) -> hasvalue (mu g) (f 0).
Proof.
  intros g f H.
  eapply mu_hasvalue. split.
  - enough (I f (f 0) = true) as <- by eapply H.
    unfold I.
    rewrite seq_app, map_app. cbn.
    rewrite app_nth1. 2: rewrite app_length, repeat_length; cbn; lia.
    rewrite app_nth2. 2: rewrite repeat_length; cbn; lia.
    now rewrite repeat_length, PeanoNat.Nat.sub_diag.
  - intros.
    enough (I f m = false) as <- by eapply H.
    unfold I.
    rewrite seq_app, map_app. cbn.
    rewrite app_nth1. 2: rewrite app_length, repeat_length; cbn; lia.
    rewrite app_nth1. 2: rewrite repeat_length; cbn; lia.
    destruct nth eqn:E; try reflexivity.
    enough (In true (repeat false (f 0))) by (eapply repeat_spec; eassumption).
    rewrite <- E. eapply nth_In. rewrite repeat_length. lia.
Qed.

Lemma flat_map_length_ge {X Y} (f : X -> list Y) l n :
  length l >= n ->
  (forall x, length (f x) > 0) ->
  length (flat_map f l) >= n.
Proof.
  intros Hl Hf. induction l in n, Hl |- *; cbn in *.
  - lia.
  - rewrite app_length. 
    destruct n; try lia.
    specialize (IHl n ltac:(lia)).
    specialize (Hf a). lia.
Qed.

Lemma R_spec g f :
  (forall x, g x =! I f x) ->
  forall x, R g x =! f x.
Proof.
  intros H x. revert g f H.
  induction x; intros; cbn.
  - now eapply R_spec0.
  - eapply bind_hasvalue. exists (f 0).
    split. now eapply R_spec0.
    eapply (IHx (fun m : nat => g (m + S (f 0))) (fun y => f (S y))).
    clear - H. intros x.
    specialize (H (x + S (f 0))).
    enough (I (fun y => f (S y)) x = I f (x + S (f 0))) as -> by eassumption. clear H.
    unfold I.
    rewrite <- map_map, seq_shift. cbn.
    symmetry.
    rewrite app_nth2. all: rewrite app_length, repeat_length. 2: cbn; lia.
    cbn.
    replace (x + S (f 0) - (f 0 + 1)) with x by lia.
    replace (x + S (f 0)) with (S (x + f 0)) by lia.
    cbn. rewrite seq_app, map_app, flat_map_app.
    rewrite app_assoc, app_nth1. reflexivity.
    rewrite !app_length, repeat_length; cbn.
    enough (length (flat_map (fun n : nat => repeat false n ++ [true]) (map f (seq 2 x)))
            >= x) by lia.
    eapply flat_map_length_ge. 
    + rewrite map_length, seq_length. lia.
    + intros. rewrite app_length, repeat_length. cbn. lia.
Qed.

Lemma SCT_bool_to_SCT :
  SCT_bool -> SCTS.
Proof.
  intros (ϕ & Hϕ & SCT).
  exists (fun c x => the_fun (R (fun x => @Build_part _ (ϕ c x) (Hϕ c x)) x)). split.
  - intros c x. eapply spec_fun.
  - intros f. specialize (SCT (fun x => I (f x))) as [γ H].
    exists γ. intros x y.
    enough (R (fun x0 : nat => {| the_fun := ϕ (γ x) x0; spec_fun := Hϕ (γ x) x0 |}) y
              =! f x y) as [n Hn] by firstorder.
    eapply R_spec. eapply H.
Qed.

