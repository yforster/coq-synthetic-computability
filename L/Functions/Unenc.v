From Undecidability.L Require Import Functions.Encoding Datatypes.LOptions Datatypes.LNat LTerm.

Print nat_unenc.

Instance term_nat_unenc : computable nat_unenc.
Proof.
  extract.
Qed.