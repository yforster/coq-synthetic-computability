From Computability.L.Tactics Require Import LTactics.
From Computability.L Require Import UpToC.
From Computability.L.Datatypes Require Export List.List_enc LNat LOptions LBool.

Set Default Proof Using "Type".

Definition c__ntherror := 15.
Definition nth_error_time (X : Type) (A : list X) (n : nat) := (min (length A) n + 1) * c__ntherror. 
Instance termT_nth_error (X:Type) (Hx : registered X): computableTime' (@nth_error X) (fun l _ => (5, fun n _ => (nth_error_time l n, tt))). 
Proof.
  extract. solverec. all: unfold nth_error_time, c__ntherror; solverec. 
Qed.

Definition c__length := 11.
Instance termT_length X `{registered X} : computableTime' (@length X) (fun A _ => (c__length * (1 + |A|),tt)).
Proof.
extract. solverec. all: unfold c__length; solverec.
Qed.


Instance term_nth X (Hx : registered X) : computableTime' (@nth X) (fun n _ => (5,fun l lT => (1,fun d _ => (n*20+9,tt)))). 
Proof.
  extract.
  solverec.
Qed.

Instance term_repeat A `{registered A}: computableTime' (@repeat A) (fun _ _ => (5, fun n _ => (n * 12 + 4,tt))).
Proof.
  extract. solverec.
Qed.


Section Fix_X.
  Context {X:Type} {intX : registered X}.

  Variable X_eqb : X -> X -> bool.
  Hypothesis X_eqb_spec : (forall (x y:X), Bool.reflect (x=y) (X_eqb x y)).
    
  Definition pos_nondec :=
    fix pos_nondec (eqb: X -> X -> bool) (s : X) (A : list X) {struct A} : option nat :=
      match A with
      | [] => None
      | a :: A0 =>
        if eqb s a
        then Some 0
        else match pos_nondec eqb s A0 with
            | Some n => Some (S n)
            | None => None
            end
      end.

  Lemma pos_nondec_spec (x:X) `{eq_dec X} A: pos_nondec X_eqb x A = pos x A.
  Proof using X_eqb_spec.
    induction A;[reflexivity|];cbn.
    rewrite IHA. destruct (X_eqb_spec x a); repeat (destruct _; try congruence).
  Defined. (* because other extract *)

  Global Instance term_pos_nondec:
    computable pos_nondec.
  Proof.
    extract.
  Defined. (* because other extract *)
End Fix_X.
