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

Definition enum_term := (fun! ⟨n,m⟩ => nth_error (list_enumerator_term n) m).

Instance enum_term_computable : computable enum_term.
Proof.
  extract.
Qed.    

Definition T_L (c : nat) (x : nat) (n : nat) :=
   match enum_term c with
   | Some t => match eva n (L.app t (enc x)) with
               | Some t => nat_unenc t
               | None => None
               end
   | None => None
   end.

Instance T_L_computable : computable T_L.
Proof.
  extract.
Qed.

Require Import Undecidability.Axioms.axioms.
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

Instance L_model_of_computation : model_of_computation.
Proof.
  unshelve econstructor.
  exact T_L.
  intros c x n1 res H1 n2 Hle. unfold T_L in *.
  destruct _ eqn:E1; try congruence.
  destruct eva eqn:E; try congruence.
  eapply eva_le in E; eauto.
  now rewrite E.
Defined.

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

(* Lemma SMN_T : exists s_1_1, forall c x y v, (exists n, T c ⟨x,y⟩ n = Some v) <-> (exists n, T (s_1_1 c y) y n = Some v). *)
(* Proof. *)
(*   exists (fun c x => if enum_term c is Some s then I_term (L.lam (L.app s (enc x)) *)

Section assume_CT.

Variable ct : @CT L_model_of_computation.

Local Definition ea : EA := (exist _ φ (CT_to_EA' ct)).
Local Definition W := W ea.

Lemma enumerator_W_code f (p : nat -> Prop) :
  enumerator f p -> computable f -> { c | forall x, W c x <-> p x}.
Proof.
  intros Hf Hcomp.
  assert (computable (fun n => if f n is Some x then S x else 0)) as [s [Hp Hs]] by extract.
  exists (I_term s). intros x. cbn in Hs. 
  unfold W, axioms.W, ea, φ. cbn. unfold T_L. split.
  - intros [nm Hnm]. destruct (unembed nm) as [n m]. cbn in *.
    destruct (enum_term) eqn:E1; try congruence.
    destruct (eva) eqn:E2; try congruence.
    destruct (nat_unenc) as [[] | ] eqn:E3; try congruence.
    inv Hnm.
    eapply Hf. exists n. rewrite I_term_correct in E1.
    specialize E1 as [= ->].
    eapply unenc_correct2 in E3 as <-.
    eapply eva_equiv in E2.
    specialize (Hs n _ eq_refl) as (? & E4 & ->). rewrite E4 in E2.
    eapply unique_normal_forms in E2. 2:Lproc. 2:Lproc.
    change (LNat.nat_enc (S x)) with (enc (S x)) in E2.
    eapply inj_enc in E2 as [= E2].
    now destruct (f n); inv E2.
  - intros [n Hn] % Hf.
    specialize (Hs n _ eq_refl) as (? & H & ->).
    edestruct equiv_eva with (s := L.app s (enc n)) as [m Hm].
    2: now rewrite H. 1: now Lproc.
    exists ⟨n,m⟩. now rewrite embedP, I_term_correct, Hm, unenc_correct, Hn.
Qed.

Lemma SMN : exists s, forall c x y, W (s c x) y <-> W c ⟨x,y⟩.
Proof.
  unshelve eexists.
  - intros c x. edestruct (enumerator_W_code) with (p := fun y => W c ⟨x,y⟩) as [r Hr].
    Unshelve. 4:{ 
      exact (fun! ⟨n,m ⟩ => if T c n m is Some (S xy) then (fun! ⟨x',y⟩ => if Nat.eqb x x' then Some y else None) xy else None). }
    + intros y. unfold W, axioms.W, ea, φ. cbn. unfold T_L. split.
      * intros [nm H]. exists nm. destruct (unembed nm) as [n m].
        destruct enum_term; try congruence.
        destruct eva; try congruence.
        destruct nat_unenc; try congruence.
        destruct n0; try congruence. inv H.
        rewrite embedP. now rewrite Nat.eqb_refl.
      * intros [nm H]. exists nm. destruct (unembed nm) as [n m].
        destruct enum_term; try congruence.
        destruct eva; try congruence.
        destruct nat_unenc; try congruence.
        destruct n0; try congruence. destruct (unembed n0) eqn:E.
        destruct (Nat.eqb_spec x n1); try congruence. subst. inv H.
        f_equal. eapply (f_equal embed) in E.
        now rewrite unembedP in E.
    +  unfold T, L_model_of_computation. extract.
    + exact r.
  - cbn. intros. destruct enumerator_W_code. eapply i.
Qed.

End assume_CT.

Theorem CT_to_EA_SMN :
  @CT L_model_of_computation ->

  exists e : nat -> nat -> option nat,                                (*  This is EA  *)
    (forall f : nat -> option nat, exists c : nat, e c≡{ran} f) /\

  let W c x := exists n, e c n = Some x in                      (* This is SMN *)
    exists s, forall c x y, W (s c x) y <-> W c ⟨x,y⟩.
Proof.
  intros ct. exists φ. split.
  - now eapply CT_to_EA'.
  - now unshelve eapply SMN.
Qed.

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
