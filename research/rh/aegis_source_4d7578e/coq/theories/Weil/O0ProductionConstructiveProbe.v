(*
  AEGIS Ω — O₀ production-carrier RED probe

  This test intentionally names the constructive production API before that API
  exists. It must be RED until AnalyticDefinitions.v migrates away from the
  classical Coq R carrier.
*)

Require Import AnalyticDefinitions.

Theorem o0_production_real_order_reflexive :
  forall x : O0RealV1,
    O0LeV1 x x.
Proof.
  intros x.
  apply o0_real_order_refl_v1.
Qed.
