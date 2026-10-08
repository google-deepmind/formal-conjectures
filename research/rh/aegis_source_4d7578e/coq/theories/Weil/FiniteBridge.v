(*
  AEGIS Ω — Weil finite bridge algebra

  This file proves only exact finite algebra over the rationals.
  It does NOT prove the analytic Guinand–Weil dictionary, the Archimedean
  operator-order theorem, global Weil positivity, or the Riemann Hypothesis.

  Intended correspondence:
  - divided-difference and pole terms mirror the finite matrix assembly shape;
  - bounded-tail lemmas justify the three-way scalar decision algebra once an
    independent theorem has established 0 <= delta <= B.
*)

From Coq Require Import QArith.QArith.
From Coq Require Import Psatz.
From Coq Require Import Ring.
From Coq Require Import Field.

Open Scope Q_scope.

Definition divided_difference
    (psi : Q -> Q) (m n : Q) : Q :=
  (psi m - psi n) / (m - n).

Definition pole_kernel
    (c s : Q -> Q) (m n : Q) : Q :=
  2 * (c m * c n - s m * s n).

Definition offdiag_entry
    (psi c s : Q -> Q) (m n : Q) : Q :=
  divided_difference psi m n + pole_kernel c s m n.

Theorem divided_difference_offdiag_symmetric :
  forall (psi : Q -> Q) (m n : Q),
    ~ m == n ->
    divided_difference psi m n == divided_difference psi n m.
Proof.
  intros psi m n Hmn.
  unfold divided_difference.
  assert (Hmn0 : ~ (m - n == 0)) by (intro H; apply Hmn; lra).
  assert (Hnm0 : ~ (n - m == 0)) by (intro H; apply Hmn; lra).
  field; lra.
Qed.

Theorem pole_kernel_symmetric :
  forall (c s : Q -> Q) (m n : Q),
    pole_kernel c s m n == pole_kernel c s n m.
Proof.
  intros c s m n.
  unfold pole_kernel.
  ring.
Qed.

Theorem offdiag_entry_symmetric :
  forall (psi c s : Q -> Q) (m n : Q),
    ~ m == n ->
    offdiag_entry psi c s m n == offdiag_entry psi c s n m.
Proof.
  intros psi c s m n Hmn.
  unfold offdiag_entry.
  setoid_rewrite (divided_difference_offdiag_symmetric psi m n Hmn).
  setoid_rewrite (pole_kernel_symmetric c s m n).
  apply Qeq_refl.
Qed.

Theorem bounded_positive_tail_preserves_nonnegative :
  forall (qT delta B : Q),
    0 <= qT ->
    0 <= delta ->
    delta <= B ->
    0 <= qT + delta.
Proof.
  intros qT delta B Hq Hdelta Hbound.
  lra.
Qed.

Theorem bounded_positive_tail_certifies_negative :
  forall (qT delta B : Q),
    0 <= delta ->
    delta <= B ->
    qT + B < 0 ->
    qT + delta < 0.
Proof.
  intros qT delta B Hdelta Hbound Hnegative.
  lra.
Qed.

Theorem gray_zone_can_change_sign :
  forall (B : Q),
    0 < B ->
    exists (qT delta_negative delta_positive : Q),
      qT < 0 /\
      0 < qT + B /\
      0 <= delta_negative /\
      delta_negative <= B /\
      qT + delta_negative < 0 /\
      0 <= delta_positive /\
      delta_positive <= B /\
      0 < qT + delta_positive.
Proof.
  intros B HB.
  exists (-(1#2) * B), 0, B.
  repeat split; lra.
Qed.
