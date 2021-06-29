Require Import Undecidability.L.Datatypes.LNat.
Require Import Undecidability.L.Datatypes.List.List_in Undecidability.L.Datatypes.List.List_basics.
Require Import Undecidability.L.Functions.Unenc.
Require Import Undecidability.Shared.ListAutomation.
Require Import Undecidability.Shared.embed_nat.

Require Import Undecidability.L.Datatypes.List.List_extra Undecidability.L.Datatypes.LProd.
Require Import Undecidability.L.Datatypes.LTerm Undecidability.L.Functions.Eval.

Import ListNotations ListAutomationNotations EmbedNatNotations.

Definition L_nat := (fix f n := match n with 0 => [0] | S n0 => f n0 ++ [S n0] end).

Instance L_T_nat_computable : computable L_nat.
Proof.
  unfold L_nat. cbn.
  extract.
Qed.

Fixpoint list_enumerator_term (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => list_enumerator_term n ++ [var m | m ∈ L_nat n] ++ [ lam s | s ∈ list_enumerator_term n ] ++ [ L.app s t | (s,t) ∈ (list_enumerator_term n × list_enumerator_term n) ]
  end.

Definition app' '(s,t) := L.app s t.

Instance app'_computable : computable app'.
Proof.
  extract.
Qed.  

Instance list_enumerator_term_computable : computable list_enumerator_term.
Proof.
  change (computable (fix FFF (n : nat) : list term :=
  match n with
  | 0 => []
  | S n => FFF n
           ++ map var (L_nat n) 
           ++ map lam (FFF n) 
           ++ map app' (list_prod (FFF n) (FFF n))
  end)). extract.
Qed.

Definition unembed' := (fix F (k : nat) := 
  match k with 0 => (0,0) | S n => match fst (F n) with 0 => (S (snd (F n)), 0) | S x => (x, S (snd (F n))) end end).

Instance unembed_computable : computable unembed.
Proof.
  eapply computableExt with (x := unembed'). 2:extract.
  intros n. cbn. induction n; cbn.
  - reflexivity.
  - fold (unembed n). rewrite IHn. now destruct (unembed n).
Qed.

(* Definition unembed' := (fix F (k : nat) :=  *)
(*                           match k with 0 => (0,0) | S n => match fst (F n) with 0 => (S (snd (F n)), 0) | S x => (x, S (snd (F n))) end end). *)

Fixpoint sum n : nat :=
  match n with
  | 0 => 0
  | S n' => S n' + sum n'
  end.

Definition encode '(x, y) : nat :=
  y + sum (y + x).

Instance sum_computable : computable sum.
Proof.
  extract.
Qed.

Instance embed_computable : computable embed.
Proof.
  change (computable encode). extract.
Qed.

Definition enum_term := (fun! ⟨n,m⟩ => nth_error (list_enumerator_term n) m).

(* Instance enum_term_computable : computable enum_term. *)
(* Proof. *)
(*   extract. *)
(* Qed.     *)

Definition enum_proc n :=
  match enum_term n with Some (lam t) =>
                         if bound_dec 0 (lam t) then Some (lam t) else None | _ => None end.

Lemma enum_proc_proc n t :
  enum_proc n = Some t -> proc t.
Proof.
  unfold enum_proc. destruct enum_term as [[]|]; try congruence.
  destruct bound_dec; try congruence.
  intros [= <-]. eapply closed_dcl in b. firstorder.
Qed.

Definition T_L (c : nat) (x : nat) (n : nat) :=
   match enum_proc c with
   | Some t => match eva n (L.app t (enc x)) with
               | Some t => nat_unenc t
               | None => None
               end
   | None => None
   end.

(* Instance T_L_computable : computable T_L. *)
(* Proof. *)
(*   extract. *)
(* Qed. *)

Require Import Undecidability.Axioms.bestaxioms.
Require Import Undecidability.L.Util.L_facts Undecidability.L.Computability.Seval.
Require Import Undecidability.Synthetic.ListEnumerabilityFacts Undecidability.Synthetic.EnumerabilityFacts Undecidability.Synthetic.DecidabilityFacts.
Require Import Undecidability.Shared.ListAutomation Undecidability.Shared.Dec.

Lemma list_enumerator_term_correct : list_enumeratorᵗ list_enumerator_term term.
Proof with (try eapply cum_ge'; eauto; lia).
  intros t. induction t as [m | t1 [n1 IH1] t2 [n2 IH2] | t [n IH]].
  - destruct (el_T m) as [n Hn]. exists (S n). cbn. in_app 2. eauto.
  - exists (1 + n1 + n2). cbn. in_app 4.
    in_collect (t1, t2)...  
  - exists (1 + n). cbn. in_app 3. eauto.
Qed.

Lemma datatype_term : {I | retraction I enum_term term nat}.
  eapply enumerator_retraction.
  2: abstract eapply list_enumeratorᵗ_enumeratorᵗ, list_enumerator_term_correct.
  unshelve eapply DecidabilityFacts.dec_decider; intros [t1 t2]; eapply term_eq_dec.
Defined.

Definition I_term := proj1_sig datatype_term.

Lemma I_term_correct s : enum_term (I_term s) = Some s.
Proof.
  unfold I_term. destruct datatype_term as [? H]. eapply H.
Qed.

Lemma I_term_correct' s : proc s -> enum_proc (I_term s) = Some s.
Proof.
  intros [H1 % closed_dcl [s' ->]].
  unfold enum_proc.
  rewrite I_term_correct.
  destruct bound_dec. reflexivity. tauto.
Qed.

Theorem SMN : SMN_for T_L.
Proof.
  red.
  unfold T_L.
  exists (fun c x => match enum_proc c with
               Some t => I_term (lam (L.app t (L.app (ext embed) (L.app (L.app (ext (@pair nat nat)) (enc x)) (var 0)))))
             | _ => c
             end).
  intros c x y v.
  destruct enum_proc eqn:E1. 2: rewrite E1; firstorder congruence.
  pose proof (Ht := enum_proc_proc E1).
  setoid_rewrite I_term_correct'.
  split.
  - intros [n H].
    destruct eva eqn:E; inv H.
    eapply unenc_correct2 in H1. subst.
    eapply eva_equiv in E.
    assert (Eq : (L.app
             (lam
                (L.app t (L.app (ext embed) (L.app (L.app (ext (@pair nat nat)) (enc x)) # 0))))
             (enc y)) == L.app t (enc ⟨ x, y ⟩)). symmetry in E. now Lsimpl.
    rewrite E in Eq.
    eapply equiv_eva in Eq as [m H].
    exists m. cbn in *.
    now rewrite H. eapply nat_enc_proc.
  - intros [n H].
    destruct eva eqn:E; inv H.
    eapply unenc_correct2 in H1. subst.
    eapply eva_equiv in E.
    assert (L.app t (enc (embed (x, y))) == nat_enc v). {
      rewrite <- E.
      symmetry. now Lsimpl. }
    eapply equiv_eva in H as [m H].
    exists m. cbn in *.
    now rewrite H. eapply nat_enc_proc.
  - Lproc.
Qed.

Definition CT_L := CT T_L.

From Undecidability.L Require Import Synthetic.

Definition CT_L_elem :=
  forall f : nat -> nat, exists t : term, closed t /\ forall n, L.eval (L.app t (enc n)) (enc (f n)).

Definition CT_L_elem_bool :=
  forall f : nat -> bool, exists t : term, closed t /\ forall n, L.eval (L.app t (enc n)) (enc (f n)).

Definition CT_L_semidecidable :=
  forall p : nat -> Prop, semi_decidable p -> L_recognisable p.

Definition CT_L_enumerable :=
  forall p : nat -> Prop, enumerable p -> L_enumerable p.

Definition CT_L_decidable :=
  forall p : nat -> Prop, decidable p -> L_decidable p.

Lemma step_beta s t u :
  t = subst s 0 u ->
  lambda u ->
  L.app (lam s) u ≻ t.
Proof.
  intros -> [? ->]. econstructor.
Qed.

Lemma CT_L_iff_CT_L_elem : CT_L <-> CT_L_elem.
Proof.
  split. 2:intros ct; split.
  - intros [H ct] f.
    specialize (ct f) as [c Hc].
    pose proof (Hc 0) as [c0 Hc0].
    unfold T_L in Hc0.
    destruct enum_proc as [t | ] eqn:Ht; try congruence.
    assert (Hcl : proc t) by now eapply enum_proc_proc. clear Hc0.
    exists t. split. eapply Hcl.
    intros x.
    specialize (Hc x) as [n Hc]. eapply eval_iff. split. 2: Lproc.
    unfold T_L in Hc. rewrite Ht in Hc.
    destruct eva as [v | ] eqn:E; try congruence.
    eapply unenc_correct2 in Hc. subst.
    eapply seval_eval, eva_seval, E.
  - intros c x n1 v H1 n2 Hle.
    unfold T_L in *.
    destruct (enum_proc c) as [t | ]; try congruence.
    destruct (eva n1) as [? | ] eqn:E ; try congruence.
    eapply eva_le with (n2 := n2) in E. 2: lia.
    now rewrite E.
  - intros f. destruct (ct f) as (t & Hcl & H).
    exists (I_term (lam (L.app t (L.var 0)))).
    intros x. specialize (H x).
    eapply eval_iff in H.
    assert (L.app (lam (L.app t # 0)) (enc x) ⇓ enc (f x)).
    { split. 2: eapply H.
      econstructor. eapply step_beta. 3: eapply H.
      2: Lproc. cbn. now rewrite Hcl. }
    eapply eval_seval in H0 as [n Hn % seval_eva].
    exists n. unfold T_L.
    rewrite I_term_correct'. 2: Lproc.
    rewrite Hn. now rewrite unenc_correct.
Qed.

Import L_Notations.

Lemma subst_closed s n u : closed s -> subst s n u = s.
Proof.
  firstorder.
Qed.

Lemma CT_L_elem_bool_iff_CT_L_decidable :
  CT_L_elem_bool <-> CT_L_decidable.
Proof.
  split.
  - intros ct p [f Hf].
    specialize (ct f) as (t & Ht1 & Ht2).
    exists f. split. 2:exact Hf.
    econstructor. exists (lam (t 0)).
    cbn. split. Lproc. intros n ? ->.
    eexists. split. 2:reflexivity.
    specialize (Ht2 n) as ? % eval_iff.
    econstructor 2.
    eapply step_beta. cbn. rewrite Ht1. reflexivity. Lproc.
    now Lsimpl.
  - intros ct f.
    specialize (ct (fun x => f x = true)) as (g & [Ht1] & Ht2). firstorder.
    exists (ext g). split. Lproc.
    intros. eapply eval_iff. Lsimpl.
    specialize (Ht2 n). destruct (g n), (f n).
    1, 4: split; try reflexivity; Lproc.
    all: try (enough (false = true) by congruence; tauto).
Qed.

Lemma CT_L_elem_to_CT_L_elem_bool :
  CT_L_elem -> CT_L_elem_bool.
Proof.
  intros ct f.
  specialize (ct (fun x => if f x then 0 else 1)) as (t & H1 & H2).
  exists (lam (t 0 (enc true) (lam (enc false)))). split. 1:Lproc.
  intros n. specialize (H2 n).
  eapply eval_iff in H2 as [H2 H2']. eapply eval_iff.
  split. 2:Lproc.
  econstructor.
  eapply step_beta with (t := t (enc n) (enc true) (lam (enc false))). 2:Lproc.
  1:{ cbn. rewrite !subst_closed; try Lproc. reflexivity. }
  Lsimpl. destruct (f n); now try Lsimpl.
Qed.

Lemma CT_L_elem_bool_to_CT_L_semidecidable :
  CT_L_elem_bool -> CT_L_semidecidable.
Proof.
  intros ct p [f Hf].
  specialize (ct (fun! ⟨x,n⟩ => f x n)) as (t & H1 & H2).
  exists f. split. 2: eapply Hf.
  econstructor. exists (lam (lam (t ((ext embed) ((ext (@pair nat nat) 1 0)))))). cbn.
  split. Lproc.
  intros. subst.
  eexists. split. 
  econstructor 2. eapply step_beta.
  cbn. rewrite !subst_closed; try Lproc. reflexivity.
  2:reflexivity. Lproc.
  split. Lproc.
  intros. subst. eexists.
  split. 2:reflexivity.
  specialize (H2 ⟨a, a0⟩).
  rewrite embedP in H2.
  etransitivity.
  econstructor 2. eapply step_beta.
  cbn. rewrite !subst_closed. all: try Lproc. reflexivity.
  reflexivity. eapply eval_iff in H2. now Lsimpl. 
Qed.

Lemma CT_L_semidecidable_to_CT_L_enumerable :
  CT_L_semidecidable -> CT_L_enumerable.
Proof.
  intros ct p Hp.
  destruct (ct p) as (f & [Hf1] & Hf2). eapply SemiDecidabilityFacts.enumerable_semi_decidable.
  eapply discrete_nat. eauto.
  eexists. split.
  2:eapply SemiDecidabilityFacts.semi_decider_enumerator.
  2: eauto. 2: exact Hf2.
  unfold nat_enum. econstructor.
  extract.
Qed.

Lemma enumerable_graph (f : nat -> nat) :
  enumerable (fun p => exists x, p = ⟨x, f x ⟩).
Proof.
  exists (fun n => Some ⟨n, f n⟩).
  split.
  - intros [? ->]. eauto.
  - intros [n [= <-]]. eauto.
Qed.

Require Import Undecidability.L.Computability.MuRec.

Lemma CT_L_enumerable_to_CT_L_elem :
  CT_L_enumerable -> CT_L_elem.
Proof.
  intros ct f.
  pose proof (enumerable_graph f); eauto.
  eapply ct in H as (g & [Hg1] & Hg2).
  pose (h := (fun x n => match g n with Some xfx =>
                                             match unembed xfx with
                                               (x', fx) => Nat.eqb x x'
                                             end
                                | _ => false end)).
  pose (h2 := (fun n => match g n with Some xfx =>
                                             match unembed xfx with
                                               (x', fx) => fx
                                             end
                                 | _ => 0 end)).
  assert (Hh : computable h) by (unfold h; extract).
  assert (Hh2 : computable h2) by (unfold h2; extract).
  exists (lam (ext h2 (mu (lam (ext h 1 0))))).
  split. Lproc.
  intros x. eapply eval_iff.
  destruct (Hg2 ⟨x,f x⟩) as [[n H] _].
  eauto.
  Lsimpl.
  edestruct (mu_complete).
  4: rewrite H0.
  - Lproc. 
  - intros n0. eexists. Lsimpl. reflexivity.
  - instantiate (1 := n). Lsimpl.
    unfold h. now rewrite H, embedP, Nat.eqb_refl. 
  - Lsimpl.
    eapply mu_sound in H0 as (m & -> % inj_enc & H2 & H3); try Lproc.
    2: intros; eexists; now Lsimpl.
    assert (Heq : h x m = true). { 
      eapply enc_extinj. rewrite <- H2. symmetry. now Lsimpl.
    }
    unfold h in Heq.
    destruct (g m) eqn:E1; try congruence.
    destruct (unembed n0) eqn:E2.
    eapply beq_nat_true in Heq as ->.
    unfold h2. rewrite E1, E2.
    enough (n2 = f n1) as ->. split. reflexivity. Lproc.
    eapply (f_equal embed) in E2. rewrite unembedP in E2.
    subst.
    specialize (Hg2 ⟨n1,n2⟩) as [_ [x HH]]. eauto.
    eapply (f_equal unembed) in HH. rewrite !embedP in HH.
    congruence.
Qed.

Set Default Goal Selector "!".

Lemma CT_L_decidable_equiv :
  CT_L -> forall p : nat -> Prop, decidable p <-> exists t, closed t /\ forall n, (p n /\ L.eval (t (enc n)) (enc true)) \/ (~ p n /\ L.eval (t (enc n)) (enc false)).
Proof.
  intros ct % CT_L_iff_CT_L_elem % CT_L_elem_to_CT_L_elem_bool % CT_L_elem_bool_iff_CT_L_decidable.
  intros p. split.
  - intros (f & [H1] & H2) % ct. exists (ext f).
    split. 1:Lproc. intros n. specialize (H2 n).
    destruct (f n) eqn:E.
    + left. split. 1:tauto.
      eapply eval_iff. Lsimpl. rewrite E. split; [ reflexivity | Lproc].
    + right. split. 1: intros ? % H2; congruence.
      eapply eval_iff. Lsimpl. rewrite E. split; [ reflexivity | Lproc].
  - intros (t & H1 & H2).
    unshelve eexists.
    + intros n.
      destruct (@informative_eval2 (t (enc n))) as [b Hb].
      1: destruct (H2 n) as [[_ H % eval_iff] | [_  H % eval_iff]]; eauto.
      destruct (term_eq_dec b (enc true)) as [-> | N1].
      1: exact true.
      destruct (term_eq_dec b (enc false)) as [-> | N2].
      1: exact false.
      exfalso.
      destruct (H2 n) as [[_ H % eval_iff] | [_ H % eval_iff]]; eauto.
      * eapply N1. eapply unique_normal_forms. 1:eapply Hb.
        1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
        destruct H as [H _]. now Lsimpl.
      * eapply N2. eapply unique_normal_forms. 1:eapply Hb.
        1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
        destruct H as [H _]. now Lsimpl.
    + intros n.
      destruct (@informative_eval2 (t (enc n))) as [b Hb]. cbn.
      destruct term_eq_dec as [-> | N1]; cbn.
      * split; intros _; try tauto.
        destruct (H2 n) as [[? H % eval_iff] | [_ H % eval_iff]]; eauto.
        enough (He : enc true = enc false) by (cbv in He; congruence).
        eapply unique_normal_forms. 1:eapply Hb.
        1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
        destruct H as [H _]. now Lsimpl.
      * destruct term_eq_dec as [-> | N2]; cbn.
        -- split; intros ?; try congruence.
           exfalso; revert H.
           destruct (H2 n) as [[_ H % eval_iff] | [? H % eval_iff]]; eauto.
           enough (He : enc true = enc false) by (cbv in He; congruence).
           eapply unique_normal_forms. 1:Lproc. 1:eapply Hb.
           destruct Hb as [Hb _]. rewrite <- Hb.
           destruct H as [H _]. now Lsimpl.
        -- exfalso.
           destruct (H2 n) as [[_ H % eval_iff] | [_ H % eval_iff]].
           ++ eapply N1. eapply unique_normal_forms. 1:eapply Hb.
              1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
              destruct H as [H _]. now Lsimpl.
           ++ eapply N2. eapply unique_normal_forms. 1:eapply Hb.
              1:Lproc. destruct Hb as [Hb _]. rewrite <- Hb.
              destruct H as [H _]. now Lsimpl.
Qed.

Lemma HaltL_semidecidable :
  semi_decidable HaltL.
Proof.
  exists (fun t n => if eva n t is Some x then true else false).
  intros t. split.
  - intros [v [n H % seval_eva] % eval_iff % eval_seval].
    exists n. now rewrite H.
  - intros [n H]. destruct eva as [v | ] eqn:E; try congruence.
    exists v. eapply eval_iff, seval_eval, eva_seval, E.
Qed.

Lemma CT_L_semidecidable_equiv :
  CT_L ->
  forall p : nat -> Prop, semi_decidable p <-> exists t, closed t /\ forall n, p n <-> HaltL (t (enc n)).
Proof.
  intros ct % CT_L_iff_CT_L_elem % CT_L_elem_to_CT_L_elem_bool % CT_L_elem_bool_to_CT_L_semidecidable. split.
  - intros (f & [H1] & H2) % ct.
    exists (lam (mu (lam (ext f 1 0)))). split. 1:Lproc. intros x. rewrite H2.
    split.
    + intros [n Hn].
      edestruct (@mu_complete (lam (ext f (enc x) 0))) as [v Hv].
      * Lproc.
      * intros n'. exists (f x n'). now Lsimpl.
      * instantiate (1 := n). Lsimpl. now rewrite Hn.
      * exists (ext v). eapply eval_iff.
        Lsimpl. rewrite Hv.  split; [ reflexivity | Lproc].
    + intros [v Hv % eval_iff].
      assert (lam (mu (lam (ext f 1 0))) (enc x) == mu (lam (ext f (enc x) 0))) by (clear Hv; now Lsimpl).
      rewrite H in Hv. edestruct (@mu_sound (lam (ext f (enc x) 0))) as [n [H3 [H4 _]]].
      3: eapply Hv.
      * Lproc.
      * intros n'. exists (f x n'). now Lsimpl.
      * now Lsimpl.
      * exists n. subst.
        eapply enc_extinj. rewrite <- H4. symmetry. now Lsimpl.
  - intros (t & H1 & H2).
    destruct (HaltL_semidecidable) as [g Hg].
    exists (fun x n => g (t (enc x)) n). red in Hg. intros x.
    now rewrite H2, Hg.
Qed.

From Undecidability Require Import principles.

Lemma CT_L_MP_equiv :
  CT_L ->
  MP <-> forall t,  ~~ (HaltL t) -> HaltL t.
Proof.
  intros ct. split.
  - intros H % MP_to_MP_semidecidable. apply H, HaltL_semidecidable.
  - intros He.
    intros f Hf.
    eapply CT_L_semidecidable_equiv with (p := fun _ => exists n, f n = true) in ct as [(t & H1 & H2) _].
    + exists (fun _ n => f n). firstorder.
    + eapply (H2 0). eapply He. now rewrite <- H2.
Qed.

From Undecidability Require Import reductions.

Lemma CT_L_enumerable_equiv :
  CT_L -> forall p : nat -> Prop, enumerable p <-> p ⪯ₘ HaltL.
Proof.
  intros ct p. rewrite <- halting.sec_enum. split.
  - intros (t & H1 & H2) % CT_L_semidecidable_equiv; eauto.
    eexists. exact H2.
  - intros [f Hf].
    destruct (HaltL_semidecidable) as [g Hg].
    exists (fun x n => g (f x) n). red in Hg. intros x. red in Hf.
    now rewrite Hf, Hg.
Qed.

(* Section assume_CT. *)

(*   Variable ct : CT T_L. *)

(*   Definition φ c := fun! ⟨ n, m ⟩ => match T_L c n m with Some (S x) => Some x | _ => None end. *)

(* (* Local Definition ea : EA := (exist _ φ (CT_to_EA' ct)). *) *)
(* (* Local Definition W := W ea. *) *)

(*   Definition W c x := exists n, φ c n = Some x. *)

(*   Lemma enumerator_W_code f (p : nat -> Prop) : *)
(*     enumerator f p -> computable f -> { c | forall x, W c x <-> p x}. *)
(*   Proof. *)
(*     intros Hf Hcomp. *)
(*     assert (computable (fun n => if f n is Some x then S x else 0)) as [s [Hp Hs]] by extract. *)
(*     exists (I_term s). intros x. cbn in Hs.  *)
(*     unfold W, φ. cbn. unfold T_L. split. *)
(*     - intros [nm Hnm]. destruct (unembed nm) as [n m]. cbn in *. *)
(*       destruct (enum_term) eqn:E1; try congruence. *)
(*       destruct (eva) eqn:E2; try congruence. *)
(*       destruct (nat_unenc) as [[] | ] eqn:E3; try congruence. *)
(*       inv Hnm. *)
(*       eapply Hf. exists n. rewrite I_term_correct in E1. *)
(*       specialize E1 as [= ->]. *)
(*       eapply unenc_correct2 in E3 as <-. *)
(*       eapply eva_equiv in E2. *)
(*       specialize (Hs n _ eq_refl) as (? & E4 & ->). rewrite E4 in E2. *)
(*       eapply unique_normal_forms in E2. 2:Lproc. 2:Lproc. *)
(*       change (LNat.nat_enc (S x)) with (enc (S x)) in E2. *)
(*       eapply inj_enc in E2 as [= E2]. *)
(*       now destruct (f n); inv E2. *)
(*     - intros [n Hn] % Hf. *)
(*       specialize (Hs n _ eq_refl) as (? & H & ->). *)
(*       edestruct equiv_eva with (s := L.app s (enc n)) as [m Hm]. *)
(*       2: now rewrite H. 1: now Lproc. *)
(*       exists ⟨n,m⟩. now rewrite embedP, I_term_correct, Hm, unenc_correct, Hn. *)
(*   Qed. *)

(*   Lemma SMN_help1: *)
(*     forall c x : nat, *)
(*       enumerator *)
(*         (fun! ⟨ n, m ⟩ => *)
(*            if T_L c n m is (Some (S xy)) *)
(*            then let (x', y) := unembed xy in if x =? x' then Some y else None else None) *)
(*         (fun y : nat => W c ⟨ x, y ⟩). *)
(*   Proof. *)
(*     intros c x. *)
(*     intros y. unfold W, φ. cbn. unfold T_L. split. *)
(*     - intros [nm H]. exists nm. destruct (unembed nm) as [n m]. *)
(*       destruct enum_term; try congruence. *)
(*       destruct eva; try congruence. *)
(*       destruct nat_unenc; try congruence. *)
(*       destruct n0; try congruence. inv H. *)
(*       rewrite embedP. now rewrite Nat.eqb_refl. *)
(*     - intros [nm H]. exists nm. destruct (unembed nm) as [n m]. *)
(*       destruct enum_term; try congruence. *)
(*       destruct eva; try congruence. *)
(*       destruct nat_unenc; try congruence. *)
(*       destruct n0; try congruence. destruct (unembed n0) eqn:E. *)
(*       destruct (Nat.eqb_spec x n1); try congruence. subst. inv H. *)
(*       f_equal. eapply (f_equal embed) in E. *)
(*       now rewrite unembedP in E. *)
(*   Qed. *)

(*   Lemma SMN : exists s, forall c x y, W (s c x) y <-> W c ⟨x,y⟩. *)
(*   Proof. *)
(*     unshelve eexists. *)
(*     - intros c x. *)
(*       unshelve refine (proj1_sig (@enumerator_W_code (fun! ⟨n,m ⟩ => if T_L c n m is Some (S xy) then (fun! ⟨x',y⟩ => if Nat.eqb x x' then Some y else None) xy else None) (fun y => W c ⟨x,y⟩) _ _)). *)
(*       + eapply SMN_help1. *)
(*       + abstract (unfold T_L; extract). *)
(*     - intros. eapply (proj2_sig (@enumerator_W_code _ (fun y => W c ⟨x,y⟩) _ _)). *)
(*   Qed. *)

(* End assume_CT. *)

(* Theorem CT_to_EA_SMN : *)
(*   (forall f : nat -> nat, *)
(*       exists c : nat, forall x : nat, exists n : nat, T_L c x n = Some (f x)) -> *)
(*   SCT. *)
(* Proof. *)
(*   intros ct. eapply EA_to_SCT. exists φ.  *)
(*   - now eapply CT_to_EA'. *)
(*   - now unshelve eapply SMN. *)
(* Qed. *)

(* Definition I_l := projT1 datatype_list_nat. *)
(* Definition R_l := proj1_sig (projT2 datatype_list_nat). *)

(* Lemma datatype_list_nat : {I & {R | retraction I R (list nat) nat}}. *)
(* Proof. *)
(*   edestruct enumerator_retraction with (X := list nat) as (I & H). *)
(*   2: exact _. *)
(*   - unshelve eapply DecidabilityFacts.dec_decider. *)
(*     intros [l1 l2]. red. repeat decide equality. *)
(*   - eauto. *)
(* Defined. *)

(* Lemma computable_has_code (f : nat -> nat) : computable f -> {c | axioms.computes c f}. *)
(* Proof. *)
(*   intros [s [Hp Hs]]. cbn in Hs. *)
(*   exists (I_term s). intros x. specialize (Hs x _ eq_refl) as (? & H & ->). *)
(*   edestruct equiv_eva with (s := L.app s (enc x)) as [n Hn]. *)
(*   2: now rewrite H. 1: now Lproc. *)
(*   exists n. unfold T, L_model_of_computation. unfold T_L. *)
(*   now rewrite I_term_correct, Hn, unenc_correct. *)
(* Qed. *)

(* Lemma List_id (l : list nat) : { c_l | forall x, W c_l x <-> List.In x l}. *)
(* Proof. *)
(*   eapply enumerator_W_code. eapply decider_enumerator. *)
(*   intros x. red. symmetry. eapply list_in_decb_iff. intros a b. eapply (decider_eq_nat (a,b)). exact _. *)
(*   cbn. extract. *)
(* Qed. *)

(* Import L_Notations_app.  *)

(* Lemma computable_iff (f : nat -> nat) : (exists c, axioms.computes c f) <-> inhabited (computable f). *)
(* Proof. *)
(*   split. *)
(*   - intros [c H]. econstructor. *)
(*     destruct (enum_term c) as [t | ] eqn:E. *)
(*     + exists (lam (L.app (ext nat_unenc) (L.app Eval (L.app (L.app (ext L.app) (enc t)) (L.app (ext (@enc nat _)) #0))) (lam #0) (enc 0))). *)
(*       cbn. split. unfold Eval. cbn. Lproc. *)
(*       intros x ? ->. exists (enc (f x)). split. 2:reflexivity. *)
(*       specialize (H x) as [n Hn]. *)
(*       Lsimpl. eapply equiv_lambda. Lproc. *)
(*       change (enc (L.app t (enc x))) with (ext (L.app t (enc x))). *)
(*       rewrite eval_Eval with (t := enc (f x)). Lsimpl. rewrite unenc_correct. Lsimpl. *)
(*       eapply seval_eval with (n := n), eva_seval. *)
(*       unfold T, L_model_of_computation, T_L in Hn. *)
(*       rewrite E in Hn. destruct (eva); try congruence. *)
(*       eapply unenc_correct2 in Hn. subst. reflexivity. *)
(*     + exfalso. specialize (H 0) as [n Hn]. cbn in Hn. unfold T_L in Hn. rewrite E in Hn. congruence. *)
(*   - intros [[c H] % computable_has_code]. eauto. Unshelve. *)
(*   unfold Eval. Lproc. *)
(* Qed. *)

(* Lemma all_computable (f : nat -> nat) : inhabited (computable f). *)
(* Proof. *)
(*   eapply computable_iff, ct. *)
(* Qed. *)

(* Lemma SMN' : forall f, exists k, forall c x, W (k c) x <-> W c (f x). *)
(* Proof. *)
(*   intros f. destruct (all_computable f) as [s [Hp H]]. *)
(*   unshelve eexists. *)
(*   - intros c. edestruct (enumerator_W_code) with (p := fun x => W c (f x)) as [r Hr]. shelve. shelve. exact r. *)
(*   - intros c x. cbn. destruct _. eapply i. *)
(*   Unshelve. *)
(*   exact (fun! ⟨n,mx⟩ => (fun! ⟨m,x⟩ => if T c n m is Some fx then if Nat.eqb (S (f x)) fx then Some x else None else None) mx). *)
(*   + intros x. unfold W, axioms.W, ea, φ. cbn. unfold T_L. split. *)
(*     * intros [nm H]. destruct (unembed nm) as [n m]. *)
(*       destruct enum_term eqn:E1; try congruence. *)
(*       destruct eva eqn:E2; try congruence. *)
(*       destruct nat_unenc as [ [] | ] eqn:E3; try congruence. *)
(*       inv H. *)
(*       eapply unenc_correct2 in E3 as <-. *)
(*       exists ⟨n, ⟨m,x⟩⟩. now rewrite !embedP, E2, unenc_correct, Nat.eqb_refl. *)
(*     * intros [nmx H]. destruct (unembed nmx) as [n mx]. *)
(*       destruct (unembed mx) as [m x']. *)
(*       destruct enum_term eqn:E1; try congruence. *)
(*       destruct eva eqn:E2; try congruence. *)
(*       destruct nat_unenc eqn:E3; try congruence. *)
(*       destruct (Nat.eqb_spec (S (f x')) n0); try congruence. subst. *)
(*       inv H. *)
(*       exists ⟨n,m⟩. now rewrite embedP, E2, E3. *)
(*   + unfold T, L_model_of_computation. extract. *)
(* Qed. *)

(* Print Assumptions SMN'. *)

(* Require Import Undecidability.Synthetic.truthtables. *)

(* Lemma bla {X} f  : decider f (fun x : X => f x = true). *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

(* Lemma TT'' :  *)
(*   forall f : nat -> { Q : list nat & truthtable (length Q)},  *)
(*     inhabited (forall l, {c_l | forall x, W c_l x <-> eval_tt (projT2 (f x)) (map (fun x => negb (inb (uncurry Nat.eqb) x l)) (projT1 (f x))) = true}). *)
(* Proof. *)
(*   intros f. econstructor. intros l. *)
(*   eapply enumerator_W_code. *)
(*   - eapply decider_enumerator. 2:exact _. eapply bla. *)
(*   -  *)
(* Admitted. *)

(* Lemma TT' :  *)
(*   forall f : nat -> { Q : list nat & truthtable (length Q)},  *)
(*     exists c : list nat -> nat, forall l x, W (c l) x <-> eval_tt (projT2 (f x)) (map (fun x => negb (inb (uncurry Nat.eqb) x l)) (projT1 (f x))) = true. *)
(* Proof. *)
(*   intros f. pose proof (TT'' f) as [F]. *)
(*   exists (fun l => proj1_sig (F l)). intros. destruct F. cbn. eapply i. *)
(* Qed. *)

(* Definition neg_tt : forall n, truthtable n -> truthtable n := fun n T => mk_tt (fun l => negb (eval_tt T l)). *)

(* Lemma neg_tt_spec n l (T : truthtable n) : *)
(*   length l = n -> *)
(*   eval_tt (neg_tt T) l = negb (eval_tt T l). *)
(* Proof. *)
(*   intros <-.  *)
(*   unfold neg_tt. *)
(*   now rewrite eval_tt_mk_tt. *)
(* Qed. *)

(* Lemma TT :  *)
(*   forall f : nat -> { Q : list nat & truthtable (length Q)},  *)
(*     exists c : list nat -> nat, forall l x, W (c l) x <-> eval_tt (projT2 (f x)) (map (fun x => negb (inb (uncurry Nat.eqb) x l)) (projT1 (f x))) = false. *)
(* Proof. *)
(*   intros f. destruct (TT' (fun n => existT (projT1 (f n)) (neg_tt (projT2 (f n))))) as [c H]. *)
(*   exists c. intros l x. *)
(*   rewrite H. destruct (f x) as [Q T]. cbn. rewrite neg_tt_spec. 2: now rewrite map_length. *)
(*   now rewrite negb_true_iff. *)
(* Qed. *)
 
