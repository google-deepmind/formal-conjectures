(* Diagnostic only: isolate the assumption surface of an R -> R carrier. *)
From Coq Require Import Reals.

Definition O0FunctionCarrierV1 := R -> R.

Theorem o0_trust_probe_function_reflexive :
  forall f : O0FunctionCarrierV1, f = f.
Proof.
  intros f.
  reflexivity.
Qed.
