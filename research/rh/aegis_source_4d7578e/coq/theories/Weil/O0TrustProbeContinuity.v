(* Diagnostic only: isolate the assumption surface introduced by continuity. *)
From Coq Require Import Reals.

Record O0ContinuousCarrierV1 := {
  o0_continuous_function :> R -> R;
  o0_continuity : continuity o0_continuous_function
}.

Theorem o0_trust_probe_continuity_reflexive :
  forall f : O0ContinuousCarrierV1, f = f.
Proof.
  intros f.
  reflexivity.
Qed.
