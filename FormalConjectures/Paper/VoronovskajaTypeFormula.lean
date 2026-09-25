/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Voronovskaja-type Formula for the Bezier Variant of the Bernstein Operators

The Bézier-type Bernstein operators $B_{n,\alpha}$ for $\alpha > 0$ are defined for
$f : [0,1] \to \mathbb{R}$ by
$$
(B_{n,\alpha} f)(x)
  = \sum_{k=0}^n f\!\left(\frac{k}{n}\right)
    \left( J_{n,k}(x)^{\alpha} - J_{n,k+1}(x)^{\alpha} \right),
$$
where
$$
J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x),
\qquad
p_{n,j}(x) = \binom{n}{j} x^j(1-x)^{n-j},
$$
and $J_{n,n+1}(x) = 0$.

In the classical case $\alpha = 1$, these operators reduce to the usual Bernstein operators.
For $f$ which are $C^2$ on $[0,1]$, one has the classical Voronovskaja
asymptotic formula
$$
\lim_{n \to \infty} n\bigl( B_{n,1} f(x) - f(x) \bigr)
    = \tfrac{1}{2} x(1-x) f''(x).
$$

## Known Results
* For $\alpha = 1$, the asymptotics are completely understood.
* Numerical experiments indicate that for $\alpha \neq 1$ the quantity
    $$
        \sqrt{n}\,\bigl( B_{n,\alpha} f(x) - f(x) \bigr)
    $$
    may converge to a non-zero limit.

## The Problem
Determine the asymptotic behaviour of the Bézier-type Bernstein operators for $\alpha > 0$,
$\alpha \neq 1$:
\textbf{Existence of the limit:}
    Prove (or disprove) the existence of the limit
    $$
        \lim_{n \to \infty}
        \sqrt{n}\,\bigl( B_{n,\alpha} f(x) - f(x) \bigr),
    $$
    at least for sufficiently smooth functions $f$.
    \textbf{Explicit form of the limit:}
    If the limit exists, determine an explicit expression for it in terms of $f$, $x$, and $\alpha$.

## Provenance

The limit formula recorded here, together with the elementary identities and the endpoint
reduction in this file, was first proposed by *Samuel Schlesinger*. The first complete proof
is the Lean 4 formalisation by *Kenta Kitamura*
([KitaKen1 on GitHub](https://github.com/KitaKen1)) in [K26], which is linked from
`voronovskaja_theorem.bezier_bernstein_operators`.

*References:*

* [Voronovskaja-type Formula for the Bézier Variant of the Bernstein Operators](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf),
  by *Ulrich Abel*, in *Constructive Theory of Functions, Sozopol 2010*.
* [K26] [A Formal Conjectures Bézier--Bernstein Theorem in
  Lean](https://github.com/KitaKen1/bezier-bernstein-voronovskaja-lean), by *Kenta Kitamura*.
-/

@[expose] public section

open Topology Filter MeasureTheory ProbabilityTheory Real unitInterval Polynomial

namespace VoronovskajaTypeFormula

/--
Cumulative sum $J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x)$.
-/
noncomputable def bernsteinTail (n k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc k n, bernsteinPolynomial ℝ n j

/--
Bézier–type Bernstein operator:
$$
(B_{n,\alpha} f)(x)
= \sum_{k=0}^{n}
f\!\left(\frac{k}{n}\right)
\left(
J_{n,k}(x)^{\alpha}
- J_{n,k+1}(x)^{\alpha}
\right)
$$
-/
noncomputable def bezierBernstein (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    f (k / n) * ((bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α)

/-- The zeroth Bernstein tail is the constant polynomial one. -/
@[category API, AMS 26 40 47]
lemma bernsteinTail_zero (n : ℕ) : bernsteinTail n 0 = 1 := by
  rw [bernsteinTail, ← Nat.range_succ_eq_Icc_zero]
  exact bernsteinPolynomial.sum ℝ n

/-- The Bernstein tail after the final index vanishes. -/
@[category API, AMS 26 40 47]
lemma bernsteinTail_succ_self (n : ℕ) : bernsteinTail n (n + 1) = 0 := by
  simp [bernsteinTail]

@[category API, AMS 26 40 47]
private lemma bernsteinTail_eq_add {n k : ℕ} (hk : k ≤ n) :
    bernsteinTail n k = bernsteinPolynomial ℝ n k + bernsteinTail n (k + 1) := by
  rw [bernsteinTail, bernsteinTail, ← Finset.insert_Icc_add_one_left_eq_Icc hk,
    Finset.sum_insert]
  simp

@[category API, AMS 26 40 47]
private lemma bernsteinPolynomial_eval_nonneg {n k : ℕ} {x : ℝ} (hx : x ∈ I) :
    0 ≤ (bernsteinPolynomial ℝ n k).eval x := by
  rw [bernsteinPolynomial]
  simp only [eval_mul, eval_natCast, eval_pow, eval_X, eval_sub, eval_one]
  rcases hx with ⟨hx0, hx1⟩
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

/-- Evaluation identifies `bernsteinTail` with the usual binomial tail polynomial. -/
@[category API, AMS 26 40 47]
lemma bernsteinTail_eval_eq_binomial_tail (n k : ℕ) (x : ℝ) :
    (bernsteinTail n k).eval x =
      ∑ j ∈ Finset.Icc k n, (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j) := by
  simp [bernsteinTail, Polynomial.eval_finsetSum, bernsteinPolynomial]

/--
The Bézier--Bernstein operator written directly in terms of the explicit binomial tails
$J_{n,k}(x) = \sum_{j=k}^{n}\binom{n}{j}x^{j}(1-x)^{n-j}$.
-/
@[category API, AMS 26 40 47]
lemma bezierBernstein_eq_sum_binomial_tail (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    bezierBernstein n α f x =
      ∑ k ∈ Finset.range (n + 1), f (k / n) *
        ((∑ j ∈ Finset.Icc k n, (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j)) ^ α -
          (∑ j ∈ Finset.Icc (k + 1) n, (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j)) ^ α) := by
  simp [bezierBernstein, bernsteinTail_eval_eq_binomial_tail]

@[category API, AMS 26 40 47]
private lemma bernsteinTail_eval_nonneg {n k : ℕ} {x : ℝ} (hx : x ∈ I) :
    0 ≤ (bernsteinTail n k).eval x := by
  rw [bernsteinTail, Polynomial.eval_finsetSum]
  exact Finset.sum_nonneg fun j hj ↦ bernsteinPolynomial_eval_nonneg hx

/-- Bernstein tails decrease as their lower index increases. -/
@[category API, AMS 26 40 47]
lemma bernsteinTail_eval_antitone {n k : ℕ} {x : ℝ} (hx : x ∈ I) :
    (bernsteinTail n (k + 1)).eval x ≤ (bernsteinTail n k).eval x := by
  by_cases hk : k ≤ n
  · rw [bernsteinTail_eq_add hk]
    simp only [eval_add]
    exact le_add_of_nonneg_left (bernsteinPolynomial_eval_nonneg hx)
  · have hnk : n < k := Nat.lt_of_not_ge hk
    have hnk' : n < k + 1 := hnk.trans (Nat.lt_succ_self k)
    simp [bernsteinTail, Finset.Icc_eq_empty_of_lt hnk, Finset.Icc_eq_empty_of_lt hnk']

/-- Every Bézier--Bernstein coefficient is nonnegative on the unit interval. -/
@[category API, AMS 26 40 47]
lemma bezier_weight_nonneg {n k : ℕ} {α x : ℝ} (hα : 0 < α) (hx : x ∈ I) :
    0 ≤ (bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α := by
  rw [sub_nonneg]
  exact Real.rpow_le_rpow (bernsteinTail_eval_nonneg hx)
    (bernsteinTail_eval_antitone hx) hα.le

/-- The Bézier--Bernstein coefficients telescope to one. -/
@[category API, AMS 26 40 47]
lemma sum_bezier_weights (n : ℕ) {α x : ℝ} (hα : 0 < α) :
    ∑ k ∈ Finset.range (n + 1),
      ((bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α) = 1 := by
  rw [Finset.sum_range_sub', bernsteinTail_zero, bernsteinTail_succ_self]
  simp [hα.ne']

@[category API, AMS 26 40 47]
private lemma sum_range_mul_sub_succ (q : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) * (q k - q (k + 1)) =
      (∑ k ∈ Finset.Icc 1 n, q k) - n * q (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hn : n = 0
      · subst n
        simp
      · rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.sum_insert]
        · push_cast
          ring
        · simp

/-- Bézier--Bernstein operators reproduce constant functions. -/
@[category API, AMS 26 40 47]
lemma bezierBernstein_const (n : ℕ) (α c x : ℝ) (hα : α ≠ 0) :
    bezierBernstein n α (fun _ ↦ c) x = c := by
  rw [bezierBernstein, ← Finset.mul_sum, Finset.sum_range_sub']
  rw [bernsteinTail_zero, bernsteinTail_succ_self]
  simp [hα]

/-- On the identity function, the operator is the normalized sum of its powered binomial tails. -/
@[category API, AMS 26 40 47]
lemma bezierBernstein_id (n : ℕ) (α x : ℝ) (hn : n ≠ 0) (hα : α ≠ 0) :
    bezierBernstein n α id x =
      (1 / n) * ∑ k ∈ Finset.Icc 1 n, (bernsteinTail n k).eval x ^ α := by
  rw [bezierBernstein]
  simp only [id_eq]
  let q : ℕ → ℝ := fun k ↦ (bernsteinTail n k).eval x ^ α
  have hq : q (n + 1) = 0 := by
    simp [q, bernsteinTail_succ_self, hα]
  calc
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n) * (q k - q (k + 1)) =
        (1 / n) * ∑ k ∈ Finset.range (n + 1), (k : ℝ) * (q k - q (k + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      field_simp
    _ = (1 / n) * ∑ k ∈ Finset.Icc 1 n, q k := by
      rw [sum_range_mul_sub_succ, hq]
      ring
    _ = _ := rfl

/--
For the identity function, the scaled approximation error is eventually exactly the centered,
powered-binomial-tail sum. This is the first-moment limit needed in the interior case.
-/
@[category API, AMS 26 40 47]
lemma eventually_scaled_bezierBernstein_id (α x : ℝ) (hα : α ≠ 0) :
    (fun n : ℕ ↦ Real.sqrt n * (bezierBernstein n α id x - x)) =ᶠ[atTop]
      fun n : ℕ ↦ ((∑ k ∈ Finset.Icc 1 n, (bernsteinTail n k).eval x ^ α) - n * x) /
        Real.sqrt n := by
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [bezierBernstein_id n α x hn hα]
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))).ne'
  have hn_real : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp
  rw [hsqrt]

/-- Bézier--Bernstein operators evaluate exactly at the left endpoint. -/
@[category API, AMS 26 40 47]
lemma bezierBernstein_zero (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (hα : α ≠ 0) :
    bezierBernstein n α f 0 = f 0 := by
  have htail (k : ℕ) : (bernsteinTail n k).eval 0 = if k = 0 then 1 else 0 := by
    simp [bernsteinTail, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_0]
  rw [bezierBernstein]
  simp [htail, hα]

/-- Bézier--Bernstein operators evaluate exactly at the right endpoint for positive degree. -/
@[category API, AMS 26 40 47]
lemma bezierBernstein_one (n : ℕ) (α : ℝ) (f : ℝ → ℝ)
    (hn : n ≠ 0) (hα : α ≠ 0) : bezierBernstein n α f 1 = f 1 := by
  have htail (k : ℕ) : (bernsteinTail n k).eval 1 = if k ≤ n then 1 else 0 := by
    simp only [bernsteinTail, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_1]
    by_cases hk : k ≤ n
    · rw [if_pos hk, Finset.sum_eq_single n]
      · simp
      · intro j hj hjn
        simp [hjn]
      · simp [hk]
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_Icc] at hj
      exact (hk (hj.1.trans hj.2)).elim
  rw [bezierBernstein]
  simp only [htail]
  rw [Finset.sum_eq_single n]
  · simp [hn, hα]
  · intro k hk hkn
    simp only [Finset.mem_range] at hk
    have hkle : k ≤ n := Nat.le_of_lt_succ hk
    have hk1le : k + 1 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_ne hkle hkn)
    simp [hkle, hk1le]
  · simp

/--
The proposed first-order bias constant for the Bézier--Bernstein operator:
\[
\mu_\alpha = \int_0^\infty
  \bigl((1-\Phi(t))^\alpha + \Phi(t)^\alpha - 1\bigr)\,dt.
\]
Here $\Phi$ is Mathlib's cumulative distribution function of the standard
Gaussian measure.
-/
noncomputable def bezierBias (α : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0,
    (1 - cdf (gaussianReal 0 1) t) ^ α + cdf (gaussianReal 0 1) t ^ α - 1

/-- Chernoff bound for the standard Gaussian: $1 - \Phi(t) \le e^{-t^2/2}$ for $t \ge 0$. -/
@[category API, AMS 26 60]
lemma one_sub_cdf_gaussianReal_le_exp {t : ℝ} (ht : 0 ≤ t) :
    1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2)) := by
  have hcompl : 1 - cdf (gaussianReal 0 1) t = (gaussianReal 0 1).real (Set.Ioi t) := by
    rw [ProbabilityTheory.cdf_eq_real, ← Set.compl_Iic, measureReal_compl measurableSet_Iic]
    simp
  have hmono : (gaussianReal 0 1).real (Set.Ioi t) ≤
      (gaussianReal 0 1).real {ω : ℝ | t ≤ id ω} :=
    measureReal_mono Set.Ioi_subset_Ici_self
  have hchernoff := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := t) t ht
    (by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t)
  rw [hcompl]
  refine hmono.trans (hchernoff.trans_eq ?_)
  rw [mgf_id_gaussianReal, ← Real.exp_add]
  norm_num
  ring_nf

@[category API, AMS 26 60]
private lemma antitone_one_sub_cdf_rpow {α : ℝ} (hα : 0 ≤ α) :
    Antitone fun t : ℝ => (1 - cdf (gaussianReal 0 1) t) ^ α := fun a b hab =>
  Real.rpow_le_rpow (by linarith [cdf_le_one (gaussianReal 0 1) b])
    (by linarith [monotone_cdf (gaussianReal 0 1) hab]) hα

@[category API, AMS 26 60]
private lemma antitone_one_sub_cdf_pow {α : ℝ} (hα : 0 ≤ α) :
    Antitone fun t : ℝ => 1 - cdf (gaussianReal 0 1) t ^ α := fun a _b hab =>
  sub_le_sub_left (Real.rpow_le_rpow (cdf_nonneg (gaussianReal 0 1) a)
    (monotone_cdf (gaussianReal 0 1) hab) hα) 1

/-- The positive-tail part of the bias integrand is integrable on $(0, \infty)$. -/
@[category API, AMS 26 60]
lemma integrableOn_one_sub_cdf_gaussianReal_rpow {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => (1 - cdf (gaussianReal 0 1) t) ^ α) (Set.Ioi 0) := by
  refine Integrable.mono ((integrable_exp_neg_mul_sq (b := α / 2) (by positivity)).integrableOn)
    (antitone_one_sub_cdf_rpow hα.le).measurable.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  have hnonneg : 0 ≤ 1 - cdf (gaussianReal 0 1) t := by
    linarith [cdf_le_one (gaussianReal 0 1) t]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hnonneg α), abs_of_nonneg (Real.exp_nonneg _)]
  refine (Real.rpow_le_rpow hnonneg (one_sub_cdf_gaussianReal_le_exp ht0) hα.le).trans_eq ?_
  rw [← Real.exp_mul]
  ring_nf

/-- The negative-tail part of the bias integrand is integrable on $(0, \infty)$. -/
@[category API, AMS 26 60]
lemma integrableOn_one_sub_cdf_gaussianReal_pow {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => 1 - cdf (gaussianReal 0 1) t ^ α) (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => 1 - cdf (gaussianReal 0 1) t ^ α)
      (volume.restrict (Set.Ioi 0)) :=
    (antitone_one_sub_cdf_pow hα.le).measurable.aestronglyMeasurable
  rcases le_or_gt α 1 with hα1 | hα1
  · refine Integrable.mono ((integrable_exp_neg_mul_sq (b := α / 2) (by positivity)).integrableOn)
      hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hnonneg : 0 ≤ 1 - cdf (gaussianReal 0 1) t := by
      linarith [cdf_le_one (gaussianReal 0 1) t]
    have hsplit : 1 ≤ cdf (gaussianReal 0 1) t ^ α + (1 - cdf (gaussianReal 0 1) t) ^ α := by
      have := Real.rpow_add_le_add_rpow (cdf_nonneg (gaussianReal 0 1) t) hnonneg hα.le hα1
      simpa using this
    have hupper : 1 - cdf (gaussianReal 0 1) t ^ α ≤ (1 - cdf (gaussianReal 0 1) t) ^ α := by
      linarith
    have hlower : 0 ≤ 1 - cdf (gaussianReal 0 1) t ^ α := by
      have := Real.rpow_le_one (cdf_nonneg (gaussianReal 0 1) t)
        (cdf_le_one (gaussianReal 0 1) t) hα.le
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlower,
      abs_of_nonneg (Real.exp_nonneg _)]
    refine hupper.trans ((Real.rpow_le_rpow hnonneg
      (one_sub_cdf_gaussianReal_le_exp ht0) hα.le).trans_eq ?_)
    rw [← Real.exp_mul]
    ring_nf
  · refine Integrable.mono
      (((integrable_exp_neg_mul_sq (b := 1 / 2) (by positivity)).const_mul α).integrableOn)
      hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hnonneg : 0 ≤ 1 - cdf (gaussianReal 0 1) t := by
      linarith [cdf_le_one (gaussianReal 0 1) t]
    have hbern : 1 - α * (1 - cdf (gaussianReal 0 1) t) ≤ cdf (gaussianReal 0 1) t ^ α := by
      have := one_add_mul_self_le_rpow_one_add (s := -(1 - cdf (gaussianReal 0 1) t))
        (by linarith [cdf_nonneg (gaussianReal 0 1) t]) hα1.le
      have hrw : 1 + -(1 - cdf (gaussianReal 0 1) t) = cdf (gaussianReal 0 1) t := by ring
      rw [hrw] at this
      linarith
    have hlower : 0 ≤ 1 - cdf (gaussianReal 0 1) t ^ α := by
      have := Real.rpow_le_one (cdf_nonneg (gaussianReal 0 1) t)
        (cdf_le_one (gaussianReal 0 1) t) hα.le
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlower,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ α * Real.exp (-(1 / 2) * t ^ 2))]
    have hstep : 1 - cdf (gaussianReal 0 1) t ^ α ≤ α * Real.exp (-(t ^ 2 / 2)) := by
      have hmul := mul_le_mul_of_nonneg_left (one_sub_cdf_gaussianReal_le_exp ht0)
        (by linarith : (0 : ℝ) ≤ α)
      linarith
    refine hstep.trans_eq ?_
    ring_nf

/--
`bezierBias` is the difference of the two tail integrals
$\int_0^\infty (1 - \Phi(t))^\alpha\,dt$ and $\int_0^\infty (1 - \Phi(t)^\alpha)\,dt$.
-/
@[category API, AMS 26 60]
lemma bezierBias_eq_sub {α : ℝ} (hα : 0 < α) :
    bezierBias α =
      (∫ t in Set.Ioi 0, (1 - cdf (gaussianReal 0 1) t) ^ α) -
        ∫ t in Set.Ioi 0, 1 - cdf (gaussianReal 0 1) t ^ α := by
  rw [bezierBias, ← integral_sub (integrableOn_one_sub_cdf_gaussianReal_rpow hα)
    (integrableOn_one_sub_cdf_gaussianReal_pow hα)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/--
On the unit interval the limit value may equivalently be written with `deriv` instead of
`iteratedDerivWithin`: at the endpoints the factor $\sqrt{x(1-x)}$ vanishes, and in the
interior $[0,1]$ is a neighbourhood of $x$.
-/
@[category API, AMS 26 40 47]
lemma bezierBias_mul_sqrt_mul_iteratedDerivWithin (α : ℝ) (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ I) :
    bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x =
      bezierBias α * Real.sqrt (x * (1 - x)) * deriv f x := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases hx0.eq_or_lt with rfl | hx0
  · simp
  rcases hx1.eq_or_lt with rfl | hx1
  · simp
  rw [iteratedDerivWithin_one, derivWithin_of_mem_nhds]
  exact Icc_mem_nhds hx0 hx1

/--
Classical Voronovskaja theorem (α = 1).

For functions $f$ that are $C^2$ on $[0,1]$, the limit:
$$
n\bigl( B_n f(x) - f(x) \bigr)
\;\longrightarrow\;
\frac{1}{2}\, x(1 - x)\, f''(x)
$$
-/
@[category research solved, AMS 26 40 47]
theorem voronovskaja_theorem.bernstein_operators
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    let f'' : ℝ := iteratedDerivWithin 2 f I x
    Tendsto (fun (n : ℕ) => (n : ℝ) * (bezierBernstein n 1 f x - f x))
    atTop
    (𝓝 ((1 / 2) * x * (1 - x) * f'')) := by
  sorry

/--
Voronovskaja-type formula for Bézier--Bernstein operators with shape parameter
$\alpha > 0$, $\alpha \neq 1$.

The source asks for sufficiently smooth functions. This concrete version uses
`ContDiffOn ℝ 2 f I` as a readable baseline regularity assumption; since the
domain is the compact interval $[0,1]$, this also explains why no separate
boundedness assumption is included here.

The limit exists and equals $\mu(\alpha)\,\sqrt{x(1-x)}\,f'(x)$, where
$\mu(\alpha) = \int_0^\infty \bigl( (1 - \Phi(t))^{\alpha}
- (1 - \Phi(t)^{\alpha}) \bigr)\,dt$ and $\Phi$ is the standard normal
distribution function.

Informal proof: the weights
$w_{n,k} = J_{n,k}(x)^{\alpha} - J_{n,k+1}(x)^{\alpha}$ are nonnegative and sum
to $1$, so the quadratic Taylor bound for $f \in C^2$ gives
$$
B_{n,\alpha} f(x) - f(x)
  = \sum_{k=0}^{n} \bigl( f(k/n) - f(x) \bigr) w_{n,k}
  = f'(x) \sum_{k=0}^{n} (k/n - x)\, w_{n,k}
    + O\Bigl( \sum_{k=0}^{n} (k/n - x)^2 w_{n,k} \Bigr).
$$
The two sums on the right satisfy
$$
\sqrt{n} \sum_{k=0}^{n} (k/n - x)\, w_{n,k}
  \longrightarrow \mu(\alpha)\,\sqrt{x(1-x)},
\qquad
\sqrt{n} \sum_{k=0}^{n} (k/n - x)^2 w_{n,k} \longrightarrow 0,
$$
so multiplying by $\sqrt{n}$ gives the stated limit.

The linked formal proof is a self-contained Lean 4 formalisation by *Kenta Kitamura*
([KitaKen1 on GitHub](https://github.com/KitaKen1)); see [K26].
-/
@[category research solved, AMS 26 40 47,
  formal_proof using lean4 at "https://github.com/KitaKen1/bezier-bernstein-voronovskaja-lean/blob/3f35c631d215b3841242275bf3ed2c59ea153a2d/Voronovskaja.lean"]
theorem voronovskaja_theorem.bezier_bernstein_operators
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1)
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
      (𝓝 ((answer(fun a g y => bezierBias a * Real.sqrt (y * (1 - y)) * iteratedDerivWithin 1 g I y) :
        ℝ → (ℝ → ℝ) → ℝ → ℝ) α f x)) := by
  sorry

/--
The answer recorded in `voronovskaja_theorem.bezier_bernstein_operators` is
$\mu_\alpha\sqrt{x(1-x)}\,f'(x)$.
-/
@[category test, AMS 26 40 47]
example (α : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    (answer(fun a g y => bezierBias a * Real.sqrt (y * (1 - y)) * iteratedDerivWithin 1 g I y) :
        ℝ → (ℝ → ℝ) → ℝ → ℝ) α f x =
      bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x := by
  rfl

/--
The proposed asymptotic formula holds unconditionally at the two endpoints of the unit interval.
-/
@[category API, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.boundary
    (α : ℝ) (hα_pos : 0 < α) (f : ℝ → ℝ) (x : ℝ) (hx : x = 0 ∨ x = 1) :
    Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
      (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x)) := by
  rcases hx with rfl | rfl
  · simp only [zero_mul, Real.sqrt_zero, mul_zero]
    have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    apply hzero.congr'
    filter_upwards with n
    rw [bezierBernstein_zero n α f hα_pos.ne']
    ring
  · simp only [sub_self, Real.sqrt_zero, mul_zero, zero_mul]
    have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    apply hzero.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [bezierBernstein_one n α f hn hα_pos.ne']
    ring

/--
Version of the asymptotic formula which treats "sufficiently smooth" as an eventual condition
in the smoothness order $m$: for all sufficiently large finite $m$, every $C^m$ function on
$[0,1]$ satisfies the formula.
-/
@[category API, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x)) := by
  filter_upwards [eventually_ge_atTop 2] with m hm f x hx hf
  exact voronovskaja_theorem.bezier_bernstein_operators α hα_pos hα f x hx
    (hf.of_le (by exact_mod_cast hm))

/--
Existence-only version of the eventual-smoothness variant. This separates the first part of the
source problem, that the scaled sequence has some limit, from the stronger task of finding an
explicit expression for that limit.
-/
@[category API, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth.limit_exists
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        ∃ L : ℝ,
          Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
            (𝓝 L) := by
  filter_upwards [variants.eventually_smooth α hα_pos hα] with m hm f x hx hf
  exact ⟨_, hm f x hx hf⟩

/--
Version of the asymptotic formula which records the sufficient smoothness order together with
the limit: the order $2$ and the formula $\mu_\alpha\sqrt{x(1-x)}\,f'(x)$ work.
-/
@[category API, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.answer_smoothness
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    let p : ℕ × ((ℝ → ℝ) → ℝ → ℝ) :=
      (2, fun g y => bezierBias α * Real.sqrt (y * (1 - y)) * iteratedDerivWithin 1 g I y)
    let m := p.1
    let limitFormula := p.2
    ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
      Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
        (𝓝 (limitFormula f x)) :=
  fun f x hx hf => voronovskaja_theorem.bezier_bernstein_operators α hα_pos hα f x hx hf

end VoronovskajaTypeFormula
