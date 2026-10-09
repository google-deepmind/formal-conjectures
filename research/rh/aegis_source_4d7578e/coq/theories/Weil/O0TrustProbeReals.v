(* Diagnostic only: isolate the assumption surface of bare Coq Reals. *)
From Coq Require Import Reals.

Theorem o0_trust_probe_reals_reflexive :
  forall x : R, x = x.
Proof.
  intros x.
  reflexivity.
Qed.
