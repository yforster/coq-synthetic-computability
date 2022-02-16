From Undecidability Require Import partial.
Require Import List Lia PeanoNat.
Import Nat.

Section sec.

Context {Part : partiality}.

Definition B := nat -> nat.
Notation "a ≡ b" := (equiv a b) (at level 50).

Definition is_modulus (M : B -> list nat) (F : B -> nat) :=
  (forall f, forall g, Forall (fun x => f x = g x) (M f) -> F f = F g).

Definition continuous {X} (F : B -> X) :=
  (forall f, exists m, forall g, Forall (fun x => f x = g x) m -> F f = F g).

Variable dec : nat -> list (nat * nat) * nat.
Variable code : list (nat * nat) -> nat -> nat.
Variable dec_spec : forall l m, dec (code l m) = (l, m).

Definition Fnct (L : list (nat * nat)) :=
  forall x y1 y2, In (x, y1) L -> In (x, y2) L -> y1 = y2.

Variable enum : nat -> list (nat * nat).
Variable enum_spec : forall l, Fnct l <-> exists n, l = enum n.

Definition prefix (l : list (nat * nat)) (β : B) :=
  Fnct l /\
  Forall (fun '(x,y) => β x = y) l.

Variable is_prefix : list (nat * nat) -> B -> bool.
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

Definition extend (L : list (nat * nat)) x :=
  match find (fun '(x', y) => x =? x') L with Some (x, y) => y | _ => 0 end.

Definition neighbourhood (f : B -> nat) M : list (nat * nat) * nat -> Prop :=
  fun '(L, m) => Fnct L /\ List.incl (M (extend L)) (map fst L) /\ forall α, prefix L α -> (* List.incl (M α) (map fst L) ->  *)f α = m.

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

Definition pref {X} (β : nat -> X) m :=
  (map (fun x : nat => (x, β x)) m).

Lemma extend_eq L :
  Fnct L ->
  Forall (fun '(x, y) => extend L x = y) L.
Proof.
  intros Hdup.
  eapply Forall_forall. intros [x y] H.
  unfold extend.
  destruct find as [[x' y'] | ] eqn:E.
  - eapply find_some in E as [E1 E2]. eapply eqb_eq in E2 as ->.
    firstorder.
  - eapply find_none in E. 2: eauto. cbn in E. eapply eqb_neq in E. congruence.
Qed.

Lemma prefix_eq:
  forall (β : B) (m : list nat) (α' : B), prefix (pref β m)  α' -> forall x : nat, In x m -> α' x = β x.
Proof.
  intros β m α [H1 H2] x Hx.
  rewrite Forall_forall in H2.
  eapply (H2 (_, _)). eapply in_map_iff.
  eauto.
Qed.

Lemma prefix_extend:
  forall L (α : B), prefix L α -> forall x : nat, In x (map fst L) -> α x = extend L x.
Proof.
  intros n α [Hdup Hp] x Hx.
  eapply prefix_eq; eauto. unfold pref.
  rewrite map_map. red. split.
  - clear. now intros ? ? ? (? & [= <- <-] & ?) % in_map_iff (? & [= <- <-] & ?) % in_map_iff.
  - eapply Forall_forall.
    intros [] ([] & [= <- <-] & ?) % in_map_iff.
    rewrite Forall_forall in Hp.
    erewrite (Hp (_, _)).
    pose proof (extend_eq n). rewrite Forall_forall in H.
    symmetry. unshelve eapply (H _ (_, _)). all: eauto.
Qed.

Lemma enumerable_neigh :
  forall F : B -> nat, forall M,
    is_modulus M F ->
    enumerable (neighbourhood F M).
Proof.
  intros F M Hcont.

  exists (fun n => let L_n := enum n in
           if  ListDec.incl_dec eq_dec (M (extend L_n)) (map fst L_n) then
             Some (L_n, F (extend L_n))
           else None).
  intros [L v]. split.
  - intros [Hdup Hneigh]. cbn.
    eapply enum_spec in Hdup as H. destruct H as [n ->].
    exists n. destruct Hneigh as [H1 H2].
    destruct ListDec.incl_dec; try tauto. 
    repeat f_equal. red in Hcont.
    eapply H2. red. split. 2: eapply extend_eq.
    all: eauto.
  - cbn. intros [n H].
    destruct (ListDec.incl_dec) as [Hi | ]; try congruence.
    inversion H; subst; clear H. split; [ eauto | ].
    eapply enum_spec. eauto. split; eauto.
    intros α Hp. symmetry. eapply Hcont.
    eapply Forall_forall. intros x Hx.
    symmetry.
    eapply prefix_extend; eauto.
Qed.

Definition apply (α : B) (β : B) : part nat :=
  thefirst (fun i => match α i with 0 => None
                            | S αi => let (l, m) := dec αi in
                                     if is_prefix l β
                                     then Some m
                                     else None end).

Lemma Fnct_pref β m :
  Fnct (pref β m).
Proof.
  now intros ? ? ? (? & [= <- <-] & ?) % in_map_iff (? & [= <- <-] & ?) % in_map_iff.
Qed.

Lemma apply_spec :
  forall F : B -> nat, forall M,
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
    destruct (Hα (map (fun x => (x, β x)) (M β ++ m), F β)) as [[n Hn] _].
    - red. rewrite !map_map. cbn. rewrite map_id.
      split. eapply Fnct_pref.
      erewrite <- Hm.
      2:{ eapply Forall_forall. intros x Hx.
          pose proof extend_eq ((map (fun x0 : nat => (x0, β x0)) (M β ++ m))).
          rewrite Forall_forall in H.
          setoid_rewrite in_map_iff in H.
          symmetry. unshelve eapply (H _ (x, β x)).
          2: eauto using in_or_app.
          eapply Fnct_pref.
      }
      split. eapply incl_appl, incl_refl. 
      intros α' Hpref. symmetry. eapply Hcont.
      eapply Forall_forall. intros x ?.
      symmetry.
      eapply prefix_eq; eauto. eapply in_app_iff; eauto.
    - exists n. rewrite Hn. rewrite dec_spec.
      rewrite is_prefix_spec'. reflexivity.
      red. split. eapply Fnct_pref. eapply Forall_forall.
      intros [] (? & [= -> ->] & ?) % in_map_iff. reflexivity.
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
  assert (neighbourhood F M (l1, x1)) as [HF1 [H1 H1']] by firstorder.
  assert (neighbourhood F M (l2, x2)) as [HF2 [H2 H2']] by firstorder.
  rewrite <- (H1' β), <- (H2' β).
  reflexivity. all: try now eassumption.
Qed.
