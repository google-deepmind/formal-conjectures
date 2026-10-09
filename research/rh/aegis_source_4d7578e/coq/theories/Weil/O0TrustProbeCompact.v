(* Diagnostic only: isolate compact-support predicates without continuity. *)
From Coq Require Import Reals.

Open Scope R_scope.

Record O0CompactCarrierV1 := {
  o0_compact_function :> R -> R;
  o0_compact_radius : R;
  o0_compact_radius_nonnegative : 0 <= o0_compact_radius;
  o0_compact_support :
    forall x : R,
      Rabs x > o0_compact_radius ->
      o0_compact_function x = 0
}.

Theorem o0_trust_probe_compact_reflexive :
  forall f : O0CompactCarrierV1, f = f.
Proof.
  intros f.
  reflexivity.
Qed.
