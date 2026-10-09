(*
  AEGIS Ω — finite Guinand–Weil entry dictionary, stage 1

  This file closes a deliberately narrow algebraic part of the concrete
  formula-to-operator bridge.  It proves, over exact rationals:

  1. the off-diagonal prime-source sign convention used by the evaluator is
     exactly a divided difference of the corresponding source function; and
  2. the rational pole closed-form template factors exactly as the rank-two
     pole kernel 2 (c_m c_n - s_m s_n).

  It does NOT prove:
  - the trigonometric prime source equals the zeta explicit-formula prime term;
  - the template parameters equal the analytic CCM pole normalization;
  - the diagonal derivative identities;
  - the archimedean entry formula or tail-order theorem;
  - the complete Guinand–Weil explicit formula;
  - global Weil positivity or RH.
*)

From Coq Require Import QArith.QArith.
From Coq Require Import Psatz.
From Coq Require Import Ring.
From Coq Require Import Field.

Require Import FiniteBridge.

Open Scope Q_scope.

Definition prime_source_from_sigma
    (sigma : Q -> Q) (x : Q) : Q :=
  - sigma x.

Definition prime_offdiag_formula
    (sigma : Q -> Q) (m n : Q) : Q :=
  (sigma m - sigma n) / (n - m).

Theorem prime_offdiag_matches_divided_difference :
  forall (sigma : Q -> Q) (m n : Q),
    ~ (m == n) ->
    prime_offdiag_formula sigma m n ==
      divided_difference (prime_source_from_sigma sigma) m n.
Proof.
  intros sigma m n Hmn.
  unfold prime_offdiag_formula, divided_difference, prime_source_from_sigma.
  assert (Hmn0 : ~ (m - n == 0)) by (intro H; apply Hmn; lra).
  assert (Hnm0 : ~ (n - m == 0)) by (intro H; apply Hmn; lra).
  field; lra.
Qed.

Definition pole_denominator
    (L k x : Q) : Q :=
  L * L + k * k * x * x.

Definition pole_c_template
    (a L k x : Q) : Q :=
  a * L / pole_denominator L k x.

Definition pole_s_template
    (a L k x : Q) : Q :=
  a * k * x / pole_denominator L k x.

Definition pole_closed_template
    (a L k m n : Q) : Q :=
  2 * a * a * (L * L - k * k * m * n) /
    (pole_denominator L k m * pole_denominator L k n).

Theorem pole_closed_template_factorizes :
  forall (a L k m n : Q),
    ~ (pole_denominator L k m == 0) ->
    ~ (pole_denominator L k n == 0) ->
    pole_closed_template a L k m n ==
      pole_kernel
        (pole_c_template a L k)
        (pole_s_template a L k)
        m n.
Proof.
  intros a L k m n Hm Hn.
  unfold pole_closed_template, pole_kernel,
         pole_c_template, pole_s_template, pole_denominator.
  unfold pole_denominator in Hm, Hn.
  assert (Hprod :
    ~ ((L * L + k * k * m * m) *
       (L * L + k * k * n * n) == 0)).
  {
    intro Hz.
    destruct (Qmult_integral _ _ Hz) as [Hzm | Hzn].
    - apply Hm. exact Hzm.
    - apply Hn. exact Hzn.
  }
  field.
  repeat split; assumption.
Qed.

Definition prime_pole_offdiag_formula
    (sigma : Q -> Q) (a L k m n : Q) : Q :=
  prime_offdiag_formula sigma m n +
  pole_closed_template a L k m n.

Theorem prime_pole_offdiag_dictionary :
  forall (sigma : Q -> Q) (a L k m n : Q),
    ~ (m == n) ->
    ~ (pole_denominator L k m == 0) ->
    ~ (pole_denominator L k n == 0) ->
    prime_pole_offdiag_formula sigma a L k m n ==
      offdiag_entry
        (prime_source_from_sigma sigma)
        (pole_c_template a L k)
        (pole_s_template a L k)
        m n.
Proof.
  intros sigma a L k m n Hmn Hm Hn.
  unfold prime_pole_offdiag_formula, offdiag_entry.
  setoid_rewrite (prime_offdiag_matches_divided_difference sigma m n Hmn).
  setoid_rewrite (pole_closed_template_factorizes a L k m n Hm Hn).
  apply Qeq_refl.
Qed.
