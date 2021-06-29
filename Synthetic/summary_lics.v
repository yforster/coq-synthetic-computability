From Undecidability Require Import simple simple_construction hypersimple hypersimple_construction myhill MoreEnumerabilityFacts ReducibilityFacts.

Theorem Myhill_Isomorphism_Theorem :
  forall X : Set, discrete X -> enumerableᵗ X ->
  forall Y : Set, discrete Y -> enumerableᵗ Y ->
  forall p : X -> Prop, forall q : Y -> Prop,
      p ⪯₁ q -> q ⪯₁ p -> exists f g, reduces_m f p q /\ reduces_m g q p /\ forall x y, f (g y) = y /\ g (f x) = x.
Proof.
  intros X [dX HdX] [eX HeX] Y [dY HdY] [eY HeY] p q [f [f_inj Hf]] [g [g_inj Hg]].
  assert (inhabited (eq_dec X)) as [eq_dec_X]  by (eapply discrete_iff; firstorder).
  assert (inhabited (eq_dec Y)) as [eq_dec_Y]  by (eapply discrete_iff; firstorder).
  destruct (enumerator_retraction _ _ _ HdX HeX) as [IX HIX].
  destruct (enumerator_retraction _ _ _ HdY HeY) as [IY HIY].
  eexists _, _. repeat eapply conj.
  - unshelve eapply f'_red; eauto; firstorder. 
  - unshelve eapply g'_red; eauto; firstorder.
  - intros. split.
    + eapply f'_g'.
    + eapply g'_f'.
Qed.

Theorem Posts_problem_many_one :
  exists p : nat -> Prop, simple p /\ enumerable p /\ ~ decidable p /\ ~ uncurry W ⪯ₘ p.
Proof.
  assert (semi_decidable (uncurry W)) as [W_sdec H_sdec]. {
    eapply enumerable_semi_decidable. eapply discrete_prod; eapply discrete_nat.
    eapply enumerable_W.
  }
  destruct (do_EA (fun _ => True)) as [c_top H_top]. {
    eapply decidable_enumerable. 2:eauto. exists (fun _ => true). firstorder.
  } 
  eexists.
  split; [ | repeat eapply conj].
  - eapply S_simple; eauto. 
  - eapply semi_decidable_enumerable. eauto. eapply S_simple; eauto.
  - eapply simple_undecidable. eapply S_simple; eauto.
  - intros H. eapply simple_m_incomplete. eapply S_simple; eauto. 
    intros q Hq.
    eapply red_m_transitive. eapply m_complete_W. eauto.
    eapply red_m_transitive with (q0 := uncurry W). eapply W_uncurry_red.
    exact H.
    Unshelve. all:eauto. firstorder.
Qed.

Theorem Posts_problem_truth_table :
  exists p : nat -> Prop, hyper_simple p /\ enumerable p /\ ~ decidable p /\ ~ uncurry W ⪯ₜₜ p.
Proof.
  destruct (@generative_enumerable_strong _ (fun! ⟨n,m⟩ => W n m)) as [f Hf].
  - eapply discrete_nat.
  - eapply enumerable_red. eapply W_uncurry_red. eauto. eauto.
    eapply enumerable_W.
  - eapply generative_W.
  - unshelve epose proof (HS_hypersimple (I := (fun! ⟨n,m⟩ => W n m)) (E_I := f) _ _ _).
    + firstorder.
    + firstorder.
    + intros ? % decidable_complement % decidable_enumerable.
      eapply not_coenumerable. 5: eapply H0. eapply W_uncurry_red'. all: eauto.
      eapply W_not_enumerable.
    + eexists. split. eapply H. repeat eapply conj.
      * eapply H.
      * eapply (HS_undec (I := (fun! ⟨n,m⟩ => W n m)) (E_I := f)). firstorder. firstorder.
        intros ? % decidable_complement % decidable_enumerable.
        eapply not_coenumerable. 5: eapply H1. eapply W_uncurry_red'. all: eauto.
        eapply W_not_enumerable.
      * intros Htt. eapply H.
        edestruct tt_complete_exceeds as [g Hg % exceeds_majorizes]. 2:eauto.
        eapply red_tt_transitive. 2: eauto.
        eapply red_mo_tt, K0_red.
Qed.

Print Assumptions Myhill_Isomorphism_Theorem.
Print Assumptions Posts_problem_many_one.
Print Assumptions Posts_problem_truth_table.
