(*
  AEGIS Ω — O₀ analytic vocabulary v1

  This file defines only the real-analysis carrier needed to state the
  finite-to-limit obligations. It does NOT identify this v1 carrier with every
  classical formulation of Weil's admissible test-function class, and it does
  NOT define the Riemann zeta function or RH.

  Trust boundary:
  - the load-bearing O₀ carrier is Coq's constructive Cauchy-real instance;
  - semantic real equality is the constructive-real setoid equality CReq,
    never Leibniz equality on the carrier;
  - the core does not import the classical Coq Reals hierarchy or Coquelicot;
  - continuity is stated directly by an epsilon-delta predicate over this
    carrier rather than imported from the classical real-analysis library.

  The constructive-reals library is marked experimental upstream. That is an
  API-stability caveat, not a mathematical authority claim.
*)

From Coq Require Import QArith.
From Coq Require Import Reals.Abstract.ConstructiveReals.
From Coq Require Import Reals.Cauchy.ConstructiveRcomplete.

Definition O0RealsV1 : ConstructiveReals := CRealConstructive.
Definition O0RealV1 : Type := CRcarrier O0RealsV1.

Definition O0LeV1 (x y : O0RealV1) : Prop :=
  CRle O0RealsV1 x y.

Definition O0LtV1 (x y : O0RealV1) : Set :=
  CRlt O0RealsV1 x y.

Definition O0LtPropV1 (x y : O0RealV1) : Prop :=
  CRltProp O0RealsV1 x y.

Definition O0EqV1 (x y : O0RealV1) : Prop :=
  CReq O0RealsV1 x y.

Definition O0ZeroV1 : O0RealV1 :=
  CR_of_Q O0RealsV1 (0%Q).

Definition O0OppV1 (x : O0RealV1) : O0RealV1 :=
  CRopp O0RealsV1 x.

Definition O0MinusV1 (x y : O0RealV1) : O0RealV1 :=
  CRminus O0RealsV1 x y.

Definition O0AbsV1 (x : O0RealV1) : O0RealV1 :=
  CRabs O0RealsV1 x.

Theorem o0_real_order_refl_v1 :
  forall x : O0RealV1, O0LeV1 x x.
Proof.
  intros x.
  apply CRle_refl.
Qed.

Definition O0ContinuousAtV1
    (g : O0RealV1 -> O0RealV1)
    (x : O0RealV1) : Prop :=
  forall eps : O0RealV1,
    O0LtPropV1 O0ZeroV1 eps ->
    exists delta : O0RealV1,
      O0LtPropV1 O0ZeroV1 delta /\
      forall y : O0RealV1,
        O0LtPropV1 (O0AbsV1 (O0MinusV1 y x)) delta ->
        O0LtPropV1
          (O0AbsV1 (O0MinusV1 (g y) (g x)))
          eps.

Definition O0ContinuousV1
    (g : O0RealV1 -> O0RealV1) : Prop :=
  forall x : O0RealV1, O0ContinuousAtV1 g x.

Record AdmissibleTestFunctionV1 := {
  test_function_v1 : O0RealV1 -> O0RealV1;
  support_radius_v1 : O0RealV1;
  support_radius_nonnegative_v1 :
    O0LeV1 O0ZeroV1 support_radius_v1;
  compact_support_v1 :
    forall x : O0RealV1,
      O0LtPropV1 support_radius_v1 (O0AbsV1 x) ->
      O0EqV1 (test_function_v1 x) O0ZeroV1;
  continuous_test_function_v1 :
    O0ContinuousV1 test_function_v1
}.

Definition QuadraticFormV1 :=
  AdmissibleTestFunctionV1 -> O0RealV1.

Definition FiniteQuadraticFamilyV1 :=
  nat -> QuadraticFormV1.

Definition pointwise_converges_v1
    (QR : FiniteQuadraticFamilyV1)
    (QW : QuadraticFormV1) : Prop :=
  forall (f : AdmissibleTestFunctionV1) (eta : O0RealV1),
    O0LtPropV1 O0ZeroV1 eta ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        O0LtPropV1
          (O0AbsV1 (O0MinusV1 (QR n f) (QW f)))
          eta.

Definition vanishing_nonnegative_error_v1
    (eps : nat -> O0RealV1) : Prop :=
  (forall n : nat, O0LeV1 O0ZeroV1 (eps n)) /\
  (forall eta : O0RealV1,
      O0LtPropV1 O0ZeroV1 eta ->
      exists N : nat,
        forall n : nat,
          (N <= n)%nat ->
          O0LtPropV1 (eps n) eta).

Definition GlobalWeilPositivityV1
    (QW : QuadraticFormV1) : Prop :=
  forall f : AdmissibleTestFunctionV1,
    O0LeV1 O0ZeroV1 (QW f).

Theorem global_weil_positivity_v1_pointwise :
  forall (QW : QuadraticFormV1),
    GlobalWeilPositivityV1 QW ->
    forall f : AdmissibleTestFunctionV1,
      O0LeV1 O0ZeroV1 (QW f).
Proof.
  intros QW H f.
  exact (H f).
Qed.
