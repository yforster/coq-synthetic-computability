From Undecidability Require Import partial.
Require Import List Lia PeanoNat.
Import Nat.

Lemma map_seq_eq {X} (f1 f2 : nat -> X) k n :
  (forall i, k <= i < n -> f1 i = f2 i) <->
  map f1 (seq k n) = map f2 (seq k n).
Admitted.

Lemma app_seq_eq {X} (β : nat -> X) k i x :
  i < k ->
  β i = nth i (map β (seq 0 k)) x.
Admitted.

Lemma app_length_inv {X} (l1 l2 l3 l4 : list X) :
  length l1 = length l2 -> l1 ++ l3 = l2 ++ l4 ->
  l1 = l2 /\ l3 = l4.
Proof.
Admitted.

Section sec.

Context {Part : partiality}.

Definition B := nat -> nat.
Notation "a ≡ b" := (equiv a b) (at level 50).

Definition is_modulus (M : B -> nat) (F : B -> nat) :=
  (forall f, forall g, Forall (fun x => f x = g x) (seq 0 (M f)) -> F f = F g).

Variable dec : nat -> list nat * nat.
Variable code : list nat -> nat -> nat.
Variable dec_spec : forall l m, dec (code l m) = (l, m).

Variable enum : nat -> list nat.
Variable enum_spec : forall l, exists n, l = enum n.

Definition prefix (l : list nat) (β : B) :=
  map β (seq 0 (length l)) = l.

Variable is_prefix : list nat -> B -> bool.
Variable is_prefix_spec : forall l β, prefix l β <-> is_prefix l β = true.

Variable thefirst : forall {X}, (nat -> option X) ↛ X.
Hypothesis thefirst_spec :
  forall X f (x : X),
    (forall n1 n2 x1 x2, f n1 = Some x1 -> f n2 = Some x2 -> x1 = x2) ->
    (exists n, f n = Some x) <-> thefirst f =! x.

Definition apply (α : B) (β : B) : part nat :=
  thefirst (fun i => let (l, m) := dec (α i) in
        if is_prefix l β
        then Some m
        else None).
  
Lemma apply_spec :
  forall F M : B -> nat,
    is_modulus M F ->
    is_modulus M M ->
    exists α, forall β, apply α β =! F β.
Proof.
  intros F M Hcont HcontM.
  pose (μ f := map f (seq 0 (M f))).

  exists (fun n => let L_n := enum n in
           let f_n x := nth x L_n 0 in
           code (μ f_n) (F f_n)).
  intros β.
  unfold apply. eapply thefirst_spec; setoid_rewrite dec_spec.
  2:{ 
    destruct (enum_spec (μ β)) as [n Hn].
    exists n. rewrite <- !Hn. clear Hn.
    assert (is_prefix (μ (fun x : nat => nth x (μ β) 0)) β = true) as ->. {
      eapply is_prefix_spec. red.
      unfold μ. rewrite map_length, seq_length.
      eapply map_seq_eq. intros i [_ Hi].
      unfold μ. eapply app_seq_eq.
      eapply lt_le_trans. eauto.
      rewrite <- (HcontM β). lia.
      eapply Forall_forall. intros x Hx % in_seq.
      eapply app_seq_eq. lia.
    }
    f_equal. unfold μ. 
    symmetry. eapply (Hcont β).
    eapply Forall_forall.
    intros x Hx % in_seq.
    eapply app_seq_eq. lia.
  }
  intros n1 n2 x1 x2 H1 H2.
  destruct is_prefix eqn:E1; inversion H1; subst; clear H1.
  destruct (is_prefix (μ (fun x : nat => nth x (enum n2) 0)) β)
           eqn:E2; inversion H2; subst; clear H2.
  eapply is_prefix_spec in E1, E2.
  red in E1, E2.
  unfold μ in *. rewrite map_length, seq_length in *.
  assert ((M (fun x : nat => nth x (enum n1) 0) <= (M (fun x : nat => nth x (enum n2) 0)))
          \/ (M (fun x : nat => nth x (enum n2) 0) <= (M (fun x : nat => nth x (enum n1) 0))))
         as [l | l] by lia.
  - eapply le_exists_sub in l as [k [Hk _]].
    rewrite add_comm in Hk.
    eapply Hcont.
    rewrite Hk in *. rewrite seq_app in E2. cbn in E2.
    rewrite !map_app in E2. eapply app_length_inv in E2 as [E2 E3].
    2: now rewrite !map_length, !seq_length.
    rewrite <- map_seq_eq in E2.
    eapply Forall_forall.
    intros x [_ Hx] % in_seq.
    assert (0 <= x < 0 + M (fun x : nat => nth x (enum n1) 0)) as Hx'' by lia.
    eapply E2 in Hx'' as Hx'.
    rewrite <- Hx'.
    rewrite <- map_seq_eq in E1.
    rewrite <- map_seq_eq in E3.
    symmetry. eapply E1. eauto.
  - (* symmetric case *) symmetry. rename E1 into EE. rename E2 into E1.
    rename EE into E2.
    eapply le_exists_sub in l as [k [Hk _]].
    rewrite add_comm in Hk.
    eapply Hcont.
    rewrite Hk in *. rewrite seq_app in E2. cbn in E2.
    rewrite !map_app in E2. eapply app_length_inv in E2 as [E2 E3].
    2: now rewrite !map_length, !seq_length.
    rewrite <- map_seq_eq in E2.
    eapply Forall_forall.
    intros x [_ Hx] % in_seq.
    assert (0 <= x < 0 + M (fun x : nat => nth x (enum n2) 0)) as Hx'' by lia.
    eapply E2 in Hx'' as Hx'.
    rewrite <- Hx'.
    rewrite <- map_seq_eq in E1.
    rewrite <- map_seq_eq in E3.
    symmetry. eapply E1. eauto.
Qed.


