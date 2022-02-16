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

Definition continuous (F : B -> nat) :=
  (forall f, exists m, forall g, Forall (fun x => f x = g x) (seq 0 m) -> F f = F g).

Variable dec : nat -> list nat * nat.
Variable code : list nat -> nat -> nat.
Variable dec_spec : forall l m, dec (code l m) = (l, m).

Variable enum : nat -> list nat.
Variable enum_spec : forall l, exists n, l = enum n.

Definition prefix (l : list nat) (β : B) :=
  map β (seq 0 (length l)) = l.

Variable is_prefix : list nat -> B -> bool.
Variable is_prefix_spec : forall l β, prefix l β <-> is_prefix l β = true.

Lemma is_prefix_spec' : forall l β, prefix l β -> is_prefix l β = true.
Proof. eapply is_prefix_spec. Qed.

Definition thefirst : forall {X}, (nat -> option X) ↛ X :=
  fun X f =>
    bind (mu_tot (fun n => match f n with None => false | _ => true end))
         (fun n => match f n with None => undef | Some x => ret x end).

Lemma thefirst_spec :
  forall X f (x : X),
    (forall n1 n2 x1 x2, f n1 = Some x1 -> f n2 = Some x2 -> x1 = x2) ->
    (exists n, f n = Some x) <-> thefirst f =! x.
Proof.
  intros X f x Hdet. unfold thefirst.
  rewrite bind_hasvalue.
  split.
  - intros [n Hn].
    edestruct mu_tot_ter as [v Hv].
    2:{ eapply mu_tot_hasvalue in Hv as Hv'.
        exists v. split. eapply Hv.
        cbn in *. destruct Hv' as [Hv' _].
        destruct (f v) eqn:E; try congruence.
        eapply ret_hasvalue_iff. eauto.
    }
    cbn. now rewrite Hn.
  - intros [a [[H1 H2] % mu_tot_hasvalue H3]].
    exists a. destruct (f a) eqn:E; try congruence.
    eapply ret_hasvalue_iff in H3 as ->.
    f_equal; eauto.
Qed.

Definition extend L x :=
  nth x L 0.

Definition neighbourhood (f : B -> nat) M : list nat * nat -> Prop :=
  fun '(L, m) => M (extend L) <= length L /\ forall α, prefix L α -> M α <= length L -> f α = m.

Definition enumerable {X} (p : X -> Prop) :=
  exists f, forall x, p x <-> exists n : nat, f n = Some x.

Lemma map_nth_seq {X} (x0 : X) l :
  map (fun n => nth n l x0) (seq 0 (length l)) = l.
Proof.
  induction l using rev_ind.
  - reflexivity.
  - cbn. rewrite app_length, seq_app, map_app.
    cbn. rewrite app_nth2. 2:lia.
    rewrite sub_diag. cbn. f_equal.
    rewrite <- IHl at 2.
    eapply map_ext_in.
    intros ? [_ ?] % in_seq. cbn in *.
    now rewrite app_nth1.
Qed.

Definition pref {X} (f : nat -> X) n :=
  map f (seq 0 n).

Lemma enumerable_neigh :
  forall F M : B -> nat,
    is_modulus M F ->
    enumerable (neighbourhood F M).
Proof.
  intros F M Hcont.
  pose (μ f := map f (seq 0 (M f))).

  exists (fun n => let L_n := enum n in
           if  M (extend L_n) <=? length L_n then
             Some (L_n, F (extend L_n))
           else None).
  intros [L v]. split.
  - intros Hneigh. cbn.
    destruct (enum_spec L) as [n ->].
    exists n. destruct Hneigh as [H1 H2].
    rewrite Compare_dec.leb_correct; eauto.
    repeat f_equal. red in Hcont.
    eapply H2. red. eapply map_nth_seq. eauto.
  - cbn. intros [n H].
    destruct (leb_spec (M (extend (enum n))) (length (enum n))); try congruence.
    inversion H; subst; clear H. split; [ eauto | ].
    intros. eapply Hcont.
    eapply Forall_forall. intros x [_ Hx] % in_seq.
    unfold extend. red in H. rewrite <- H.
    eapply app_seq_eq. lia.
Qed.

Definition apply (α : B) (β : B) : part nat :=
  thefirst (fun i => match α i with 0 => None
                            | S αi => let (l, m) := dec αi in
                                     if is_prefix l β
                                     then Some m
                                     else None end).

Lemma apply_spec :
  forall F M : B -> nat,
    is_modulus M F ->
    continuous M ->
    exists α, forall β, apply α β =! F β.
Proof.
  intros F M Hcont HcontM.

  destruct (enumerable_neigh F M Hcont) as [α Hα].
  exists (fun n => match α n with None => 0 | Some (x1, x2) => S (code x1 x2) end).
  intros β. unfold apply. eapply thefirst_spec.
  2:{
    destruct (HcontM β) as [m Hm].
    destruct (Hα (map β (seq 0 (M β + m)), F β)) as [[n Hn] _].
    - red. rewrite map_length, seq_length.
      erewrite <- Hm.
      2:{ eapply Forall_forall. intros x [_ Hx] % in_seq.
          eapply app_seq_eq. lia. }
      split. lia.
      intros. eapply Hcont.
      eapply Forall_forall. intros x [_ Hx] % in_seq.
      red in H. rewrite map_length, seq_length in H.
      eapply ext_in_map. exact H.
      eapply in_seq. lia.
    - exists n. rewrite Hn. rewrite dec_spec.
      rewrite is_prefix_spec'. reflexivity.
      red. now rewrite map_length, seq_length.
  }
  clear HcontM.
  intros n1 n2 x1 x2 H1 H2.
  destruct (α n1) as [[l1 v1] | ] eqn:Eα1; try congruence.
  destruct (α n2) as [[l2 v2] | ] eqn:Eα2; try congruence.
  rewrite dec_spec in *.
  destruct is_prefix eqn:E1; inversion H1; subst; clear H1.
  destruct (is_prefix l2 β)
           eqn:E2; inversion H2; subst; clear H2.
  eapply is_prefix_spec in E1, E2.
  red in E1, E2.
  assert (neighbourhood F M (l1, x1)) as [H1 H1'] by firstorder.
  assert (neighbourhood F M (l2, x2)) as [H2 H2'] by firstorder.
  assert (length l1 <= length l2 \/ length l2 <= length l1)
         as [l | l] by lia.
  - eapply le_exists_sub in l as [k [Hk _]].
    rewrite add_comm in Hk.
    rewrite <- (H1' (extend l1)), <- (H2' (extend l2)); try lia.
    2, 3: eapply map_nth_seq.
    eapply Hcont. eapply Forall_forall. intros x [_ Hx] % in_seq.
    cbn in *.
    rewrite <- E1, <- E2. unfold extend.
    rewrite Hk. rewrite seq_app, map_app.
    rewrite app_nth1. 2: rewrite map_length, seq_length; lia.
    reflexivity.
  - symmetry. rename E1 into EE. rename E2 into E1.
    rename EE into E2.
     eapply le_exists_sub in l as [k [Hk _]].
    rewrite add_comm in Hk.
    rewrite <- (H1' (extend l1)), <- (H2' (extend l2)); try lia.
    2, 3: eapply map_nth_seq.
    eapply Hcont. eapply Forall_forall. intros x [_ Hx] % in_seq.
    cbn in *.
    rewrite <- E1, <- E2. unfold extend.
    rewrite Hk. rewrite seq_app, map_app.
    rewrite app_nth1. 2: rewrite map_length, seq_length; lia.
    reflexivity.
Qed.
