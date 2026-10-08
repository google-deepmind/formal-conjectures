(** AEGIS Ω — concrete finite Guinand–Weil semantics v1. *)
From Coq Require Import Arith.PeanoNat Lia.
Require Import CoRN.reals.NRootIR.
Require Import CoRN.complex.CComplex.
Require Import VonMangoldtCanonicalBridge.
Require Import CanonicalPrimeSourceSum.

Definition finite_guinand_weil_prime_index_v1 (n : nat) : nat := S n.

Theorem concrete_index_semantics_v1 :
  finite_guinand_weil_prime_index_v1 0 = 1 /\
  forall i : nat,
    finite_guinand_weil_prime_index_v1 (S i) = canonical_integer_q_v1 i.
Proof. split; [reflexivity|intro i; reflexivity]. Qed.

Lemma concrete_von_mangoldt_one_zero_v1 : von_mangoldt_v1 1 [=] [0].
Proof.
  apply von_mangoldt_v1_zero_off_prime_powers.
  intros p k Hp Hk Hpow.
  destruct Hp as [Hp_gt1 _].
  pose proof (pow_exponent_bound p k ltac:(lia)) as Hexp.
  rewrite Hpow in Hexp. lia.
Qed.

Theorem concrete_von_mangoldt_semantics_v1 :
  von_mangoldt_v1 (finite_guinand_weil_prime_index_v1 0) [=] [0] /\
  forall i : nat,
    von_mangoldt_v1 (finite_guinand_weil_prime_index_v1 (S i))
      [=] von_mangoldt_v1 (canonical_integer_q_v1 i).
Proof.
  split; [exact concrete_von_mangoldt_one_zero_v1|intro i; apply eq_reflexive].
Qed.

Definition finite_prime_positive_integer_ir_v1 (n : nat) : IR := nring (S n).
Lemma finite_prime_positive_integer_ir_positive_v1 :
  forall n : nat, [0] [<] finite_prime_positive_integer_ir_v1 n.
Proof. intro n; unfold finite_prime_positive_integer_ir_v1; apply nring_pos; lia. Qed.

Definition finite_prime_reciprocal_ir_v1 (n : nat) : IR :=
  [1] [/] finite_prime_positive_integer_ir_v1 n
    [//] pos_ap_zero _ _ (finite_prime_positive_integer_ir_positive_v1 n).

Definition finite_prime_scalar_term_cc_v1 (f : IR -> CC) (n : nat) : CC :=
  cc_IR (von_mangoldt_v1 (finite_guinand_weil_prime_index_v1 n)) [*]
  (f (finite_prime_positive_integer_ir_v1 n) [+]
   cc_IR (finite_prime_reciprocal_ir_v1 n) [*]
   f (finite_prime_reciprocal_ir_v1 n)).

Definition canonical_q_reciprocal_ir_v1 (i : nat) : IR :=
  finite_prime_reciprocal_ir_v1 (S i).

Definition canonical_q_prime_scalar_term_cc_v1 (f : IR -> CC) (i : nat) : CC :=
  cc_IR (von_mangoldt_v1 (canonical_integer_q_v1 i)) [*]
  (f (canonical_integer_q_ir_v1 i) [+]
   cc_IR (canonical_q_reciprocal_ir_v1 i) [*]
   f (canonical_q_reciprocal_ir_v1 i)).

Theorem finite_prime_scalar_term_leading_zero_v1 :
  forall f : IR -> CC, finite_prime_scalar_term_cc_v1 f 0 [=] ([0] : CC).
Proof.
  intro f.
  unfold finite_prime_scalar_term_cc_v1, finite_guinand_weil_prime_index_v1.
  astepl (cc_IR [0] [*]
    (f (finite_prime_positive_integer_ir_v1 0) [+]
     cc_IR (finite_prime_reciprocal_ir_v1 0) [*]
     f (finite_prime_reciprocal_ir_v1 0))).
  - Step_final ([0] : CC).
Qed.

Theorem finite_prime_scalar_term_tail_index_v1 :
  forall (f : IR -> CC) (i : nat),
    finite_prime_scalar_term_cc_v1 f (S i) [=]
    canonical_q_prime_scalar_term_cc_v1 f i.
Proof.
  intros f i.
  unfold finite_prime_scalar_term_cc_v1, canonical_q_prime_scalar_term_cc_v1,
    finite_guinand_weil_prime_index_v1, finite_prime_positive_integer_ir_v1,
    finite_prime_reciprocal_ir_v1, canonical_q_reciprocal_ir_v1,
    canonical_integer_q_ir_v1, canonical_integer_q_v1.
  apply eq_reflexive.
Qed.

Theorem concrete_prime_term_semantics_v1 :
  (forall f : IR -> CC, finite_prime_scalar_term_cc_v1 f 0 [=] ([0] : CC)) /\
  (forall (f : IR -> CC) (i : nat),
      finite_prime_scalar_term_cc_v1 f (S i) [=]
      canonical_q_prime_scalar_term_cc_v1 f i).
Proof. split; [exact finite_prime_scalar_term_leading_zero_v1|exact finite_prime_scalar_term_tail_index_v1]. Qed.

Definition finite_pole_term_cc_v1 (mellin_zero mellin_one : CC) : CC :=
  mellin_zero [+] mellin_one.
Theorem concrete_pole_term_semantics_v1 :
  forall mellin_zero mellin_one : CC,
    finite_pole_term_cc_v1 mellin_zero mellin_one [=] mellin_zero [+] mellin_one.
Proof. intros; unfold finite_pole_term_cc_v1; apply eq_reflexive. Qed.

Definition finite_archimedean_normalization_cc_v1
    (constant_at_one integral_value : CC) : CC := constant_at_one [+] integral_value.
Theorem concrete_archimedean_normalization_v1 :
  forall constant_at_one integral_value : CC,
    finite_archimedean_normalization_cc_v1 constant_at_one integral_value [=]
    constant_at_one [+] integral_value.
Proof. intros; unfold finite_archimedean_normalization_cc_v1; apply eq_reflexive. Qed.

Definition finite_positive_prefix_member_v1 (count m : nat) : Prop :=
  (1 <= m <= S count)%nat.
Definition finite_coq_tail_member_v1 (count i : nat) : Prop := (i < count)%nat.

Theorem concrete_cutoff_semantics_v1 :
  von_mangoldt_v1 (finite_guinand_weil_prime_index_v1 0) [=] [0] /\
  (forall count i : nat,
      finite_coq_tail_member_v1 count i ->
      finite_positive_prefix_member_v1 count
        (finite_guinand_weil_prime_index_v1 (S i)) /\
      finite_guinand_weil_prime_index_v1 (S i) = canonical_integer_q_v1 i) /\
  (forall count m : nat,
      (2 <= m <= S count)%nat ->
      exists i : nat,
        finite_coq_tail_member_v1 count i /\ m = canonical_integer_q_v1 i).
Proof.
  split; [exact concrete_von_mangoldt_one_zero_v1|].
  split.
  - intros count i Hi; split.
    + unfold finite_coq_tail_member_v1 in Hi.
      unfold finite_positive_prefix_member_v1, finite_guinand_weil_prime_index_v1; lia.
    + reflexivity.
  - intros count m Hm; exists (m - 2)%nat; split.
    + unfold finite_coq_tail_member_v1; lia.
    + unfold canonical_integer_q_v1; lia.
Qed.

Inductive FiniteWeilMeasureConventionV1 : Type :=
| OrdinaryLebesgueV1
| MultiplicativeHaarV1.
Definition finite_explicit_integral_measure_v1 : FiniteWeilMeasureConventionV1 := OrdinaryLebesgueV1.
Definition finite_autocorrelation_inner_measure_v1 : FiniteWeilMeasureConventionV1 := OrdinaryLebesgueV1.
Theorem concrete_measure_semantics_v1 :
  finite_explicit_integral_measure_v1 = OrdinaryLebesgueV1 /\
  finite_autocorrelation_inner_measure_v1 = OrdinaryLebesgueV1 /\
  OrdinaryLebesgueV1 <> MultiplicativeHaarV1.
Proof. split; [reflexivity|split; [reflexivity|discriminate]]. Qed.

Definition finite_autocorrelation_integrand_cc_v1
    (g_xy conj_g_y : CC) : CC := g_xy [*] conj_g_y.

Theorem concrete_autocorrelation_semantics_v1 :
  (forall g_xy conj_g_y : CC,
      finite_autocorrelation_integrand_cc_v1 g_xy conj_g_y [=]
      g_xy [*] conj_g_y) /\
  finite_autocorrelation_inner_measure_v1 = OrdinaryLebesgueV1.
Proof.
  split.
  - intros; unfold finite_autocorrelation_integrand_cc_v1; apply eq_reflexive.
  - reflexivity.
Qed.

Inductive FiniteFourierFrequencyConventionV1 : Type :=
| AngularFrequencyV1
| CyclesFrequencyV1.

Inductive FiniteFourierBridgeScaleV1 : Type :=
| DivideByTwoPiV1
| IdentityFrequencyScaleV1.

Inductive FiniteFourierInversePrefactorV1 : Type :=
| OneOverTwoPiV1
| UnitInversePrefactorV1.

Definition finite_frozen_fourier_frequency_v1 : FiniteFourierFrequencyConventionV1 :=
  AngularFrequencyV1.
Definition finite_mathlib_fourier_frequency_v1 : FiniteFourierFrequencyConventionV1 :=
  CyclesFrequencyV1.
Definition finite_mellin_to_mathlib_scale_v1 : FiniteFourierBridgeScaleV1 :=
  DivideByTwoPiV1.
Definition finite_frozen_fourier_inverse_prefactor_v1 : FiniteFourierInversePrefactorV1 :=
  OneOverTwoPiV1.
Definition finite_mellin_measure_v1 : FiniteWeilMeasureConventionV1 :=
  OrdinaryLebesgueV1.

Theorem concrete_fourier_mellin_normalization_v1 :
  finite_frozen_fourier_frequency_v1 = AngularFrequencyV1 /\
  finite_mathlib_fourier_frequency_v1 = CyclesFrequencyV1 /\
  finite_mellin_to_mathlib_scale_v1 = DivideByTwoPiV1 /\
  finite_frozen_fourier_inverse_prefactor_v1 = OneOverTwoPiV1 /\
  finite_mellin_measure_v1 = OrdinaryLebesgueV1 /\
  AngularFrequencyV1 <> CyclesFrequencyV1 /\
  DivideByTwoPiV1 <> IdentityFrequencyScaleV1.
Proof.
  repeat split; try reflexivity; discriminate.
Qed.

Inductive FiniteAutocorrelationProjectionModeV1 : Type :=
| ComplexAutocorrelationCarrierV1
| RealProjectedAutocorrelationCarrierV1.

Inductive FiniteAutocorrelationSymmetryV1 : Type :=
| ReciprocalConjugateJacobianV1.

Definition finite_autocorrelation_projection_mode_v1 :
    FiniteAutocorrelationProjectionModeV1 :=
  ComplexAutocorrelationCarrierV1.
Definition finite_autocorrelation_symmetry_v1 :
    FiniteAutocorrelationSymmetryV1 :=
  ReciprocalConjugateJacobianV1.
Definition finite_autocorrelation_pointwise_real_v1 : bool := false.

Theorem concrete_complex_real_projection_v1 :
  finite_autocorrelation_projection_mode_v1 = ComplexAutocorrelationCarrierV1 /\
  finite_autocorrelation_symmetry_v1 = ReciprocalConjugateJacobianV1 /\
  finite_autocorrelation_pointwise_real_v1 = false /\
  ComplexAutocorrelationCarrierV1 <> RealProjectedAutocorrelationCarrierV1.
Proof. repeat split; try reflexivity; discriminate. Qed.

Inductive FiniteExplicitIdentityOrientationV1 : Type :=
| ZeroSideEqualsPoleMinusRhsV1.
Inductive FiniteMomentZeroOrientationV1 : Type :=
| RhsEqualsNegativeZeroSumV1.
Inductive FiniteSignInferenceStatusV1 : Type :=
| SignInequalityNotImpliedV1
| SignInequalityProvedV1.
Inductive FiniteExplicitIdentityProofStatusV1 : Type :=
| MathProvedExternalDependenciesV1
| WholeIdentityLeanKernelOpenV1
| WholeIdentityLeanKernelProvedV1.

Definition finite_explicit_identity_orientation_v1 : FiniteExplicitIdentityOrientationV1 :=
  ZeroSideEqualsPoleMinusRhsV1.
Definition finite_moment_zero_orientation_v1 : FiniteMomentZeroOrientationV1 :=
  RhsEqualsNegativeZeroSumV1.
Definition finite_sign_inference_status_v1 : FiniteSignInferenceStatusV1 :=
  SignInequalityNotImpliedV1.
Definition finite_explicit_identity_proof_status_v1 : FiniteExplicitIdentityProofStatusV1 :=
  MathProvedExternalDependenciesV1.
Definition finite_whole_identity_lean_status_v1 : FiniteExplicitIdentityProofStatusV1 :=
  WholeIdentityLeanKernelOpenV1.

Theorem concrete_sign_orientation_v1 :
  finite_explicit_identity_orientation_v1 = ZeroSideEqualsPoleMinusRhsV1 /\
  finite_moment_zero_orientation_v1 = RhsEqualsNegativeZeroSumV1 /\
  finite_sign_inference_status_v1 = SignInequalityNotImpliedV1 /\
  finite_explicit_identity_proof_status_v1 = MathProvedExternalDependenciesV1 /\
  finite_whole_identity_lean_status_v1 = WholeIdentityLeanKernelOpenV1 /\
  SignInequalityNotImpliedV1 <> SignInequalityProvedV1 /\
  WholeIdentityLeanKernelOpenV1 <> WholeIdentityLeanKernelProvedV1.
Proof. repeat split; try reflexivity; discriminate. Qed.

(** Aggregate semantics bundle.  Every field is exactly one already-closed
    constituent obligation; this record adds no stronger analytic claim. *)
Record ConcreteFiniteGuinandWeilSemanticsBundleV1 : Prop := {
  bundle_index_v1 :
    finite_guinand_weil_prime_index_v1 0 = 1 /\
    forall i : nat,
      finite_guinand_weil_prime_index_v1 (S i) = canonical_integer_q_v1 i;

  bundle_von_mangoldt_v1 :
    von_mangoldt_v1 (finite_guinand_weil_prime_index_v1 0) [=] [0] /\
    forall i : nat,
      von_mangoldt_v1 (finite_guinand_weil_prime_index_v1 (S i)) [=]
      von_mangoldt_v1 (canonical_integer_q_v1 i);

  bundle_prime_term_v1 :
    (forall f : IR -> CC, finite_prime_scalar_term_cc_v1 f 0 [=] ([0] : CC)) /\
    (forall (f : IR -> CC) (i : nat),
      finite_prime_scalar_term_cc_v1 f (S i) [=]
      canonical_q_prime_scalar_term_cc_v1 f i);

  bundle_pole_term_v1 :
    forall mellin_zero mellin_one : CC,
      finite_pole_term_cc_v1 mellin_zero mellin_one [=]
      mellin_zero [+] mellin_one;

  bundle_archimedean_v1 :
    forall constant_at_one integral_value : CC,
      finite_archimedean_normalization_cc_v1 constant_at_one integral_value [=]
      constant_at_one [+] integral_value;

  bundle_cutoff_v1 :
    von_mangoldt_v1 (finite_guinand_weil_prime_index_v1 0) [=] [0] /\
    (forall count i : nat,
      finite_coq_tail_member_v1 count i ->
      finite_positive_prefix_member_v1 count
        (finite_guinand_weil_prime_index_v1 (S i)) /\
      finite_guinand_weil_prime_index_v1 (S i) = canonical_integer_q_v1 i) /\
    (forall count m : nat,
      (2 <= m <= S count)%nat ->
      exists i : nat,
        finite_coq_tail_member_v1 count i /\ m = canonical_integer_q_v1 i);

  bundle_measure_v1 :
    finite_explicit_integral_measure_v1 = OrdinaryLebesgueV1 /\
    finite_autocorrelation_inner_measure_v1 = OrdinaryLebesgueV1 /\
    OrdinaryLebesgueV1 <> MultiplicativeHaarV1;

  bundle_autocorrelation_v1 :
    (forall g_xy conj_g_y : CC,
      finite_autocorrelation_integrand_cc_v1 g_xy conj_g_y [=]
      g_xy [*] conj_g_y) /\
    finite_autocorrelation_inner_measure_v1 = OrdinaryLebesgueV1;

  bundle_fourier_mellin_v1 :
    finite_frozen_fourier_frequency_v1 = AngularFrequencyV1 /\
    finite_mathlib_fourier_frequency_v1 = CyclesFrequencyV1 /\
    finite_mellin_to_mathlib_scale_v1 = DivideByTwoPiV1 /\
    finite_frozen_fourier_inverse_prefactor_v1 = OneOverTwoPiV1 /\
    finite_mellin_measure_v1 = OrdinaryLebesgueV1 /\
    AngularFrequencyV1 <> CyclesFrequencyV1 /\
    DivideByTwoPiV1 <> IdentityFrequencyScaleV1;

  bundle_projection_v1 :
    finite_autocorrelation_projection_mode_v1 = ComplexAutocorrelationCarrierV1 /\
    finite_autocorrelation_symmetry_v1 = ReciprocalConjugateJacobianV1 /\
    finite_autocorrelation_pointwise_real_v1 = false /\
    ComplexAutocorrelationCarrierV1 <> RealProjectedAutocorrelationCarrierV1;

  bundle_sign_orientation_v1 :
    finite_explicit_identity_orientation_v1 = ZeroSideEqualsPoleMinusRhsV1 /\
    finite_moment_zero_orientation_v1 = RhsEqualsNegativeZeroSumV1 /\
    finite_sign_inference_status_v1 = SignInequalityNotImpliedV1 /\
    finite_explicit_identity_proof_status_v1 = MathProvedExternalDependenciesV1 /\
    finite_whole_identity_lean_status_v1 = WholeIdentityLeanKernelOpenV1 /\
    SignInequalityNotImpliedV1 <> SignInequalityProvedV1 /\
    WholeIdentityLeanKernelOpenV1 <> WholeIdentityLeanKernelProvedV1
}.

Theorem concrete_finite_guinand_weil_semantics_v1 :
  ConcreteFiniteGuinandWeilSemanticsBundleV1.
Proof.
  constructor.
  - exact concrete_index_semantics_v1.
  - exact concrete_von_mangoldt_semantics_v1.
  - exact concrete_prime_term_semantics_v1.
  - exact concrete_pole_term_semantics_v1.
  - exact concrete_archimedean_normalization_v1.
  - exact concrete_cutoff_semantics_v1.
  - exact concrete_measure_semantics_v1.
  - exact concrete_autocorrelation_semantics_v1.
  - exact concrete_fourier_mellin_normalization_v1.
  - exact concrete_complex_real_projection_v1.
  - exact concrete_sign_orientation_v1.
Qed.
