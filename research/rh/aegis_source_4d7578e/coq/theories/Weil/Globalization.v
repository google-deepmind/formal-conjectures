(*
  AEGIS Ω — O₀ globalization obligations v1

  This module proves the abstract finite-to-limit order step on the constructive
  O₀ real carrier.  It does not identify QW with the classical Weil form and it
  does not prove the Weil criterion or RH.
*)

From Coq Require Import QArith Lra Field.
From Coq Require Import Reals.Abstract.ConstructiveReals.
Require Import AnalyticDefinitions.

Definition FiniteLowerBoundV1
    (QR : FiniteQuadraticFamilyV1)
    (eps : nat -> O0RealV1) : Prop :=
  forall (n : nat) (f : AdmissibleTestFunctionV1),
    O0LeV1 (O0OppV1 (eps n)) (QR n f).

Definition GlobalizationReadyV1
    (QR : FiniteQuadraticFamilyV1)
    (QW : QuadraticFormV1)
    (eps : nat -> O0RealV1) : Prop :=
  pointwise_converges_v1 QR QW /\
  vanishing_nonnegative_error_v1 eps /\
  FiniteLowerBoundV1 QR eps.

Definition GlobalizationTargetV1
    (QW : QuadraticFormV1) : Prop :=
  GlobalWeilPositivityV1 QW.

Theorem finite_lower_bound_v1_specialize :
  forall (QR : FiniteQuadraticFamilyV1) (eps : nat -> O0RealV1),
    FiniteLowerBoundV1 QR eps ->
    forall (n : nat) (f : AdmissibleTestFunctionV1),
      O0LeV1 (O0OppV1 (eps n)) (QR n f).
Proof.
  intros QR eps H n f.
  exact (H n f).
Qed.

Lemma o0_plus_minus_cancel_v1 :
  forall x y : O0RealV1,
    O0EqV1
      (CRplus O0RealsV1 y (O0MinusV1 x y))
      x.
Proof.
  intros x y.
  unfold O0EqV1, O0MinusV1.
  rewrite <- (CRplus_assoc y x (CRopp O0RealsV1 y)).
  rewrite (CRplus_comm y x).
  rewrite (CRplus_assoc x y (CRopp O0RealsV1 y)).
  rewrite CRplus_opp_r.
  rewrite CRplus_0_r.
  reflexivity.
Qed.

Lemma o0_rational_half_balance_v1 :
  forall q : Q,
    O0EqV1
      (CRplus O0RealsV1
        (CR_of_Q O0RealsV1 q)
        (CR_of_Q O0RealsV1 ((- q / 2)%Q)))
      (O0OppV1 (CR_of_Q O0RealsV1 ((- q / 2)%Q))).
Proof.
  intro q.
  unfold O0EqV1, O0OppV1.
  transitivity (CR_of_Q O0RealsV1 ((q + (- q / 2))%Q)).
  - apply CReq_sym.
    apply CR_of_Q_plus.
  - transitivity (CR_of_Q O0RealsV1 ((- (- q / 2))%Q)).
    + apply CR_of_Q_morph.
      field.
    + apply CR_of_Q_opp.
Qed.

Theorem globalization_ready_implies_global_weil_positivity_v1 :
  forall
    (QR : FiniteQuadraticFamilyV1)
    (QW : QuadraticFormV1)
    (eps : nat -> O0RealV1),
    GlobalizationReadyV1 QR QW eps ->
    GlobalizationTargetV1 QW.
Proof.
  intros QR QW eps Hready.
  destruct Hready as [Hconv [Heps Hlower]].
  destruct Heps as [_ Heps_vanish].
  unfold GlobalizationTargetV1, GlobalWeilPositivityV1.
  intro f.
  unfold O0LeV1.
  intro Hnegative.

  destruct (CR_Q_dense O0RealsV1 (QW f) O0ZeroV1 Hnegative)
    as [q [Hfq Hq0]].
  assert (Hq0_Q : (q < 0)%Q).
  {
    unfold O0ZeroV1 in Hq0.
    exact (lt_CR_of_Q O0RealsV1 q 0 Hq0).
  }

  set (eta := CR_of_Q O0RealsV1 ((- q / 2)%Q)).
  assert (Heta : CRlt O0RealsV1 O0ZeroV1 eta).
  {
    unfold eta, O0ZeroV1.
    apply CR_of_Q_lt.
    unfold Qdiv.
    assert (Hnegq : (0 < - q)%Q).
    {
      change ((- 0)%Q < (- q)%Q).
      exact (Qopp_lt_compat q 0 Hq0_Q).
    }
    assert (Htwo : (0 < 2)%Q).
    {
      unfold Qlt.
      cbn.
      reflexivity.
    }
    assert (Hinv2 : (0 < / 2)%Q).
    {
      exact (Qinv_lt_0_compat 2 Htwo).
    }
    exact (Qmult_lt_0_compat (- q) (/ 2) Hnegq Hinv2).
  }
  assert (HetaProp : O0LtPropV1 O0ZeroV1 eta).
  {
    unfold O0LtPropV1.
    exact (CRltForget O0RealsV1 O0ZeroV1 eta Heta).
  }

  destruct (Hconv f eta HetaProp) as [Nc HconvN].
  destruct (Heps_vanish eta HetaProp) as [Ne HepsN].
  set (n := Nat.max Nc Ne).
  specialize (HconvN n (Nat.le_max_l Nc Ne)).
  specialize (HepsN n (Nat.le_max_r Nc Ne)).
  specialize (Hlower n f).

  unfold O0LtPropV1 in HconvN, HepsN.
  pose proof
    (CRltEpsilon O0RealsV1
      (O0AbsV1 (O0MinusV1 (QR n f) (QW f))) eta HconvN)
    as Hclose.
  pose proof
    (CRltEpsilon O0RealsV1 (eps n) eta HepsN)
    as Heps_lt.

  assert (Hdiff_abs :
    O0LeV1
      (O0MinusV1 (QR n f) (QW f))
      (O0AbsV1 (O0MinusV1 (QR n f) (QW f)))).
  {
    unfold O0LeV1, O0AbsV1.
    destruct
      (proj2
        (CRabs_def O0RealsV1
          (O0MinusV1 (QR n f) (QW f))
          (CRabs O0RealsV1 (O0MinusV1 (QR n f) (QW f))))
        (CRle_refl
          (CRabs O0RealsV1 (O0MinusV1 (QR n f) (QW f)))))
      as [H _].
    exact H.
  }
  pose proof
    (CRle_lt_trans
      (O0MinusV1 (QR n f) (QW f))
      (O0AbsV1 (O0MinusV1 (QR n f) (QW f)))
      eta Hdiff_abs Hclose)
    as Hdiff_lt.

  pose proof
    (@CRplus_lt_compat_l O0RealsV1
      (QW f)
      (O0MinusV1 (QR n f) (QW f))
      eta Hdiff_lt)
    as Hupper0.
  rewrite (o0_plus_minus_cancel_v1 (QR n f) (QW f)) in Hupper0.
  pose proof
    (CRplus_lt_compat_r
      (R:=O0RealsV1)
      eta (QW f) (CR_of_Q O0RealsV1 q) Hfq)
    as Hq_upper.
  pose proof
    (CRlt_trans
      (QR n f)
      (CRplus O0RealsV1 (QW f) eta)
      (CRplus O0RealsV1 (CR_of_Q O0RealsV1 q) eta)
      Hupper0 Hq_upper)
    as Hupper1.
  unfold eta in Hupper1.
  rewrite (o0_rational_half_balance_v1 q) in Hupper1.

  pose proof
    (CRopp_gt_lt_contravar
      (R:=O0RealsV1) eta (eps n) Heps_lt)
    as Hopp.
  pose proof
    (CRlt_le_trans
      (O0OppV1 eta)
      (O0OppV1 (eps n))
      (QR n f)
      Hopp Hlower)
    as Hlower_strict.
  pose proof (CRlt_asym (O0OppV1 eta) (QR n f) Hlower_strict)
    as Hlower_le.

  exact (Hlower_le Hupper1).
Qed.
