(*
  AEGIS Ω — Weil criterion boundary v1

  This module intentionally does not declare a proposition named
  RiemannHypothesis and does not state a Weil-positivity -> RH theorem.

  Reason: this repository slice does not yet contain a concrete, machine-defined
  analytically continued Riemann zeta object plus the explicit-formula identity
  needed to make that theorem non-circular. The missing theorem is represented
  as status, not as Axiom/Parameter/Admitted authority.
*)

Require Import Globalization.

Inductive WeilCriterionStatusV1 : Set :=
| WEIL_CRITERION_NOT_MACHINE_BOUND.

Definition weil_criterion_status : WeilCriterionStatusV1 :=
  WEIL_CRITERION_NOT_MACHINE_BOUND.
