From Undecidability Require Import EA equiv_on SemiDecidabilityFacts Definitions reductions EnumerabilityFacts.

Import EmbedNatNotations.

Set Default Goal Selector "!".

Lemma Rice {p : nat -> Prop} c_bot c :
  (forall x, ~ W c_bot x) ->
  (forall c1 c2, W c1 ≡{_} W c2 -> p c1 -> p c2) ->
  ~ p c ->
  p c_bot -> compl K0 ⪯ₘ p.
Proof.
  intros Hbot Hequiv Hc Hpbot.
  edestruct EAP with (p := fun x y => K0 x /\ W c y) as [f Hf]. {
    exists (fun x => fun! ⟨n,m⟩ => if φ x n is Some x' then if Nat.eqb x x' then φ c m else None else None).
    intros x y. split.
    + intros [[n H1] [m H2]]. exists ⟨n,m⟩. now rewrite embedP, H1, PeanoNat.Nat.eqb_refl, H2.
    + intros [nm H]. destruct (unembed nm) as [n m].
      destruct φ as [x' | ] eqn:E; try congruence.
      destruct (PeanoNat.Nat.eqb_spec x x') as [-> | ]; try congruence.
      firstorder.
  } 
  exists f. intros x. unfold K0, compl.
  split.
  - intros H. eapply Hequiv. 2:exact Hpbot.
    cbn. intros. rewrite <- (Hf x x0). firstorder.
  - intros H. intros Hx.
    apply Hc. eapply Hequiv. 2: exact H.
    intros y. rewrite <- (Hf x y). firstorder.
Qed.

(* Lemma enumerable_prod X Y (p : X -> Prop) (q : Y -> Prop) : *)
(*   enumerable p -> enumerable q -> enumerable (uncurry (fun x y => p x /\ q y)). *)
(* Proof. *)
(*   intros [f Hf] [g Hg]. *)
(*   exists (fun! ⟨n,m⟩ => match f n, g m with Some x, Some y => Some (x, y) | _, _ => None end). *)
(*   intros (x,y). split; cbn. *)
(*   - intros [[n1 H1] % Hf [n2 H2] % Hg]. *)
(*     exists ⟨n1,n2⟩. now rewrite embedP, H1, H2. *)
(*   - intros [nm H]. destruct (unembed nm) as [n m]. *)
(*     destruct (f n) eqn:E1, (g m) eqn:E2; try congruence. *)
(*     inv H. *)
(*     split. firstorder. firstorder. *)
(* Qed. *)

Lemma Rice_Theorem {p : nat -> Prop} :
  (forall c1 c2, W c1 ≡{_} W c2 -> p c1 -> p c2) ->
  (exists c1, p c1) ->
  (exists c2, ~ p c2) -> ~ decidable p.
Proof.
  intros Hequiv [c1 Hc1] [c2 Hc2] Hp.
  destruct (do_EA (fun _ => False)) as [c_bot Hbot].
  - exists (fun _ => None). firstorder congruence.
  - destruct (DecidabilityFacts.decidable_decide Hp c_bot).
    + eapply K0_undecidable, red_m_transports; eauto.
      eapply Rice with (c_bot0 := c_bot); eauto; firstorder.
    + eapply DecidabilityFacts.decidable_complement in Hp.
      eapply K0_undecidable, red_m_transports; eauto.
      eapply Rice with (c_bot0 := c_bot) (c := c1).
      2:{ intros ? ? ? ? ?. eapply H1, Hequiv; eauto. firstorder. }
      all: firstorder.
Qed.


Module EPF.

Axiom Part : partiality.

Axiom Θ : nat -> (nat ↛ nat).

Instance equiv_part `{partiality} {A} : equiv_on (part A) := {| equiv_rel := @partial.equiv _ A |}.

Axiom EPFP : forall f : nat -> nat ↛ nat, exists γ, forall x, Θ (γ x) ≡{nat ↛ nat} f x.

Lemma FP : forall f, exists e, Θ e ≡{_} Θ (f e).
Proof.
  intros f.
  pose (h := fun x y => bind (Θ x x) (fun e => Θ e y)).
  destruct (EPFP h)  as [γ Hγ].
  destruct (EPFP (fun _ x => ret (f (γ x))))  as [γ' Hc].
  pose (c := γ' 0).
  exists (γ c).
  rewrite Hγ. unfold h.
  intros x v. rewrite bind_hasvalue. split.
  - now intros (y & <- % Hc % ret_hasvalue_inv & H2).
  - intros Hv. eexists. split; eauto.
    eapply Hc. now eapply ret_hasvalue.
Qed.

Lemma Rice_Theorem' {p : nat -> Prop} :
  (forall c1 c2, Θ c1 ≡{_} Θ c2 -> p c1 -> p c2) ->
  (exists c1, p c1) ->
  (exists c2, ~ p c2) -> ~ decidable p.
Proof.
  intros Hequiv [c1 Hc1] [c2 Hc2] [f Hf].
  pose (h x := if f x then Θ c2 else Θ c1).
  destruct (EPFP h) as [γ H].
  destruct (FP γ) as [c Hc].
  rewrite H in Hc. unfold h in Hc.
  destruct (f c) eqn:E.
  - assert (Hx : p c) by firstorder.
    eapply Hc2. eapply Hequiv. 2: eapply Hx. eapply Hc.
  - assert (Hx : ~ p c) by firstorder congruence.
    eapply Hx. eapply Hequiv. 1:symmetry; eapply Hc. exact Hc1.
Qed.

End EPF.
