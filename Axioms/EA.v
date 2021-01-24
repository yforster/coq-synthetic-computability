From Undecidability Require Import Synthetic.DecidabilityFacts Synthetic.SemiDecidabilityFacts Synthetic.EnumerabilityFacts Synthetic.ListEnumerabilityFacts reductions partial embed_nat ReducibilityFacts truthtables.
Require Import Setoid Program Lia List.

Axiom φ : nat -> nat -> option nat.

Axiom EAB : forall p, enumerable p <-> exists c, enumerator (φ c) p.

Definition W c x := exists n, φ c n = Some x.

Lemma W_spec : forall p, enumerable p <-> exists c, forall x, p x <-> W c x.
Proof.
  eapply EAB.
Qed.

Lemma do_EA p : enumerable p -> exists c, forall x, p x <-> W c x.
Proof.
  eapply W_spec.
Qed.

Axiom s : nat -> nat -> nat.

Axiom SMN : forall c x y, W (s c x) y <-> W c ⟨x,y⟩.

Definition EAs := exists φ, forall p : nat -> nat -> Prop, enumerable (fun! ⟨x,y⟩ => p x y) ->
                                        exists c : nat -> nat, forall x, enumerator (φ (c x)) (p x).

Lemma EAS' :
  forall p : nat -> nat -> Prop, enumerable (fun! ⟨x,y⟩ => p x y) ->
                                        exists c : nat -> nat, forall x y, W (c x) y <-> p x y.
Proof.
  intros p Hp.
  destruct (do_EA _ Hp) as [c Hc].
  exists (fun x => s c x). intros x y.
  now rewrite SMN, <- Hc, embedP.
Qed.

Lemma EAS :
  forall p : nat -> nat -> Prop, enumerable (uncurry p) ->
                                        exists c : nat -> nat, forall x y, W (c x) y <-> p x y.
Proof.
  intros p Hp. eapply EAS'.
  eapply enumerable_red. 4: exact Hp.
  exists (fun! ⟨x,y⟩ => (x,y)).
  - intros xy. now destruct (unembed xy) as [x y].
  - eauto.
  - now eapply discrete_prod; eapply discrete_nat.
Qed.

Lemma EAS_datatype X (p : X -> nat -> Prop) (x0 : X) :
  datatype X ->
  enumerable (uncurry p) ->
  exists c : X -> nat, forall x y, W (c x) y <-> p x y.
Proof.
  intros (I & R & HIR) Ep.
  destruct (EAS (fun x y => if R x is Some l then p l y else p x0 y)) as [c Hc].
  - eapply enumerable_red.
    4: eapply Ep.
    + exists (fun '(x, y) => if R x is Some l then (l,y) else (x0, y)).
      intros [x y]. cbn.
      destruct (R x); reflexivity.
    + eauto.
    + eapply discrete_prod. eapply datatype_discrete. now exists I, R.
      eapply discrete_nat.
  - exists (fun l => c (I l)). intros. now rewrite Hc, HIR.
Qed.

Lemma EAS_list (p : list nat -> nat -> Prop) : enumerable (uncurry p) ->
                                      exists c : list nat -> nat, forall x y, W (c x) y <-> p x y.
Proof.
  intros. eapply EAS_datatype; eauto.
  - exact nil.
  - eapply enumerable_discrete_datatype.
    eapply discrete_list, discrete_nat.
    eauto. 
Qed.

Lemma List_id : exists c_l, forall (l : list nat), forall x, W (c_l l) x <-> List.In x l.
Proof.
  eapply EAS_list.
  eapply decidable_enumerable. 2:eauto.
  eapply decidable_iff. econstructor.
  intros [x y]. cbn. exact _. 
Qed.

Notation π1 := (fun! ⟨x, y⟩ => x).
Notation π2 := (fun! ⟨x, y⟩ => y).

Lemma enumerable_W : enumerable (fun '(x, y) => W x y).
Proof.
  exists (fun p => let (n,m) := unembed p in if φ n m is Some m then Some (n, m) else None).
  intros [n m].
  split.
  - intros H.
    cbv in H. destruct H as [n' H].
    exists (embed (n, n')). rewrite embedP. cbn. now rewrite H.
  - unfold W.
    intros [p H].
    destruct (unembed p) as [n' m'].
    exists m'.
    destruct (φ n' m') eqn:E; inversion H; now subst.
Qed.

Lemma W_maximal (p : nat -> Prop) :
  enumerable p -> p ⪯ₘ uncurry W.
Proof.
  intros Hp.
  destruct (do_EA p Hp) as [c Hc].
  exists (fun x => (c, x)). exact Hc.
Qed.

Lemma SMN' : forall f, exists k, forall c x, W (k c) x <-> W c (f x).
Proof.
  intros f.
  eapply EAS.
  eapply enumerable_red with (q := uncurry W).
  - exists (fun '(x,y) => (x, f y)). now intros [x y].
  - eauto.
  - eapply discrete_prod; now eapply discrete_nat.
  - eapply enumerable_W.
Qed.

Lemma TT : 
  forall f : nat -> { Q : list nat & truthtable}, 
    exists c : list nat -> nat, forall l x, W (c l) x <-> eval_tt (projT2 (f x)) (List.map (fun x => negb (inb (uncurry Nat.eqb) x l)) (projT1 (f x))) = false.
Proof.
  intros f.
  eapply EAS_list.
  eapply decidable_enumerable. 2:eauto.
  eapply decidable_iff. econstructor.
  intros [x y]. cbn. exact _. 
Qed.


Tactic Notation "intros" "⟨" ident(n) "," ident(m) "⟩" :=
  let nm := fresh "nm" in
  let E := fresh "E" in
  intros nm; destruct (unembed nm) as [n m] eqn:E.

Lemma EAS_datatype_direct X (p : X -> nat -> Prop) (x0 : X) :
  datatype X ->
  enumerable (uncurry p) ->
  exists c : X -> nat, forall x y, W (c x) y <-> p x y.
Proof.
  intros (I & R & (R' & HIR) % (retraction_to_tight _ _ _) ) Hp.
  assert (enumerable (fun! ⟨n,m⟩ => if R' n is Some x then p x m else False)). {
    destruct Hp as [e He].
    exists (fun n => if e n is Some (x, m) then Some ⟨I x, m⟩ else None).
    intros ⟨n,m⟩.
    split.
    - destruct (R' n) eqn:ER; [ intros [n' H] % (He (_,_)) | intros []].
      exists n'. rewrite H. f_equal.
      rewrite <- embedP. rewrite unembedP.
      rewrite <- (@unembedP nm), E. repeat f_equal. now eapply HIR.
    - intros [n' H]. destruct (e n') as [ [x m'] | ] eqn:E2; try congruence.
      inv H. rewrite embedP in E. inv E. destruct (HIR x) as [-> _].
      eapply (He (_,_)). eauto.
  }

  destruct (do_EA _ H) as [c Hc].
  exists (fun x => s c (I x)).
  intros x y.
  rewrite SMN, <- Hc, embedP.
  now destruct (HIR x) as [-> _].
Qed.

Definition K0 c := W c c.

Lemma K0_not_enumerable : ~ enumerable (compl K0).
Proof.
  intros [c Hc] % do_EA. specialize (Hc c).
  unfold K0, compl in Hc. tauto.
Qed.

Lemma W_uncurry_red:
  (fun! ⟨ n, m ⟩ => W n m) ⪯ₘ uncurry W.
Proof.
  exists (fun! ⟨n,m⟩ => (n,m)). intros nm. destruct (unembed nm) as [n m]. reflexivity.
Qed.

Lemma K0_red:
  K0 ⪯ₘ uncurry W.
Proof.
  exists (fun n => (n,n)). intros n. reflexivity.
Qed.

Lemma W_uncurry_red':
  uncurry W ⪯ₘ (fun! ⟨ n, m ⟩ => W n m).
Proof.
  exists (fun '(n,m) => ⟨n,m⟩). intros [n m]. now rewrite embedP.
Qed.

Hint Resolve discrete_prod discrete_nat : core.

Lemma W_not_enumerable : ~ enumerable (compl (uncurry W)).
Proof.
  eapply not_coenumerable; eauto.
  - eapply K0_red.
  - eapply K0_not_enumerable. 
Qed.

Lemma K0_enum : enumerable K0.
Proof.
  eapply enumerable_red with (q := uncurry W).
  eapply K0_red. all:eauto.
  eapply enumerable_W.
Qed.

Lemma red_tt_not_red_m :
  compl K0 ⪯ₜₜ K0 /\ ~ compl K0 ⪯ₘ K0.
Proof.
  split.
  - eapply red_tt_complement.
  - intros H % enumerable_red.
    + now eapply K0_not_enumerable.
    + eauto.
    + eapply discrete_nat.
    + eapply K0_enum.
Qed.

Notation "m-complete p" := (forall q : nat -> Prop, enumerable q -> q ⪯ₘ p) (at level 10).

Lemma m_complete_W :
  m-complete (fun! ⟨n,m⟩ =>  W n m).
Proof.
  intros q [c Hc] % do_EA.
  exists (fun x => ⟨c,x⟩). intros x.
  now rewrite embedP.
Qed.

Lemma enum_iff (p : nat -> Prop) : enumerable p <-> semi_decidable p.
Proof.
  split.
  - intros H. eapply enumerable_semi_decidable. eapply discrete_nat. eassumption.
  - intros H. eapply semi_decidable_enumerable. eauto. eauto.
Qed.

Lemma generative_W :   generative (fun! ⟨ n, m ⟩ => W n m).
Proof.
  eapply unbounded_generative. intros x y; destruct (PeanoNat.Nat.eq_dec x y); eauto.
  destruct (do_EA (fun _ => True)) as [c_top H_top]. {
    eapply decidable_enumerable. 2:eauto. exists (fun _ => true). firstorder.
  }
  intros n. exists (map (fun m => ⟨c_top,m⟩) (seq 0 n)). split.
  now rewrite map_length, seq_length. split.
  eapply NoDup_map. intros ? ? E % (f_equal unembed). rewrite !embedP in E. congruence. eapply seq_NoDup.
  intros ? (? & <- & ?) % in_map_iff. rewrite embedP. firstorder.
Qed.
