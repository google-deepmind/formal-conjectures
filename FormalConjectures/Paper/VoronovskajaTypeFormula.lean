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

import FormalConjectures.Util.ProblemImports

/-!
# Voronovskaja-type Formula for the Bezier Variant of the Bernstein Operators

The Bézier-type Bernstein operators $B_{n,\alpha}$ for $\alpha > 0$ are defined for
$f : [0,1] \to \mathbb{R}$ by
\[
(B_{n,\alpha} f)(x)
  = \sum_{k=0}^n f\!\left(\frac{k}{n}\right)
    \left( J_{n,k}(x)^{\alpha} - J_{n,k+1}(x)^{\alpha} \right),
\]
where
\[
J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x),
\qquad
p_{n,j}(x) = \binom{n}{j} x^j(1-x)^{n-j},
\]
and $J_{n,n+1}(x) = 0$.

In the classical case $\alpha = 1$, these operators reduce to the usual Bernstein operators.
For $f$ which are $C^2$ on $[0,1]$, one has the classical Voronovskaja
asymptotic formula
\[
\lim_{n \to \infty} n\bigl( B_{n,1} f(x) - f(x) \bigr)
    = \tfrac{1}{2} x(1-x) f''(x).
\]

## Known Results
* For $\alpha = 1$, the asymptotics are completely understood.
* Numerical experiments indicate that for $\alpha \neq 1$ the quantity
    \[
        \sqrt{n}\,\bigl( B_{n,\alpha} f(x) - f(x) \bigr)
    \]
    may converge to a non-zero limit.

## The Problem
Determine the asymptotic behaviour of the Bézier-type Bernstein operators for $\alpha > 0$,
$\alpha \neq 1$:
\textbf{Existence of the limit:}
    Prove (or disprove) the existence of the limit
    \[
        \lim_{n \to \infty}
        \sqrt{n}\,\bigl( B_{n,\alpha} f(x) - f(x) \bigr),
    \]
    at least for sufficiently smooth functions $f$.
    \textbf{Explicit form of the limit:}
    If the limit exists, determine an explicit expression for it in terms of $f$, $x$, and $\alpha$.

*References:*

* [Voronovskaja-type Formula for the Bézier Variant of the Bernstein Operators](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf),
  by *Ulrich Abel*, in *Constructive Theory of Functions, Sozopol 2010*.
-/
open Topology Filter MeasureTheory ProbabilityTheory Real unitInterval Polynomial
namespace VoronovskajaTypeFormula

/--
Cumulative sum $J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x)$.
-/
noncomputable def bernsteinTail (n k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc k n, bernsteinPolynomial ℝ n j

/--
Bézier–type Bernstein operator:
\[
(B_{n,\alpha} f)(x)
= \sum_{k=0}^{n}
f\!\left(\frac{k}{n}\right)
\left(
J_{n,k}(x)^{\alpha}
- J_{n,k+1}(x)^{\alpha}
\right)
\]
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
  simp [bernsteinTail, Polynomial.eval_finset_sum, bernsteinPolynomial]

@[category API, AMS 26 40 47]
private lemma bernsteinTail_eval_nonneg {n k : ℕ} {x : ℝ} (hx : x ∈ I) :
    0 ≤ (bernsteinTail n k).eval x := by
  rw [bernsteinTail, Polynomial.eval_finset_sum]
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
    simp [bernsteinTail, Polynomial.eval_finset_sum, bernsteinPolynomial.eval_at_0]
  rw [bezierBernstein]
  simp [htail, hα]

/-- Bézier--Bernstein operators evaluate exactly at the right endpoint for positive degree. -/
@[category API, AMS 26 40 47]
lemma bezierBernstein_one (n : ℕ) (α : ℝ) (f : ℝ → ℝ)
    (hn : n ≠ 0) (hα : α ≠ 0) : bezierBernstein n α f 1 = f 1 := by
  have htail (k : ℕ) : (bernsteinTail n k).eval 1 = if k ≤ n then 1 else 0 := by
    simp only [bernsteinTail, Polynomial.eval_finset_sum, bernsteinPolynomial.eval_at_1]
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

/--
Classical Voronovskaja theorem (α = 1).

For functions $f$ that are $C^2$ on $[0,1]$, the limit:
\[
n\bigl( B_n f(x) - f(x) \bigr)
\;\longrightarrow\;
\frac{1}{2}\, x(1 - x)\, f''(x)
\]
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
Conjecture: Voronovskaja-type formula for Bézier--Bernstein operators
with shape parameter $\alpha > 0$, $\alpha \neq 1$.

A proposed answer for the limit is
\[
\mu_\alpha\sqrt{x(1-x)}\,f'(x).
\]
This candidate is recorded here for future investigation, but is not asserted
in the theorem statement.

The source asks for sufficiently smooth functions. This concrete version uses
`ContDiffOn ℝ 2 f I` as a readable baseline regularity assumption; since the
domain is the compact interval $[0,1]$, this also explains why no separate
boundedness assumption is included here. The variants below record the unknown
smoothness threshold more explicitly.

*Reference:* [Abel's source problem](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf).
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1)
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
      (𝓝 answer(sorry)) := by
  sorry

/--
The proposed asymptotic formula holds unconditionally at the two endpoints of the unit interval.

*Reference:* [Abel's source problem](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf).
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
Variant of the Bézier-Bernstein Voronovskaja problem which treats "sufficiently smooth" as an
eventual condition in the smoothness order $m$: for all sufficiently large finite $m$, every
$C^m$ function on $[0,1]$ should have the asserted asymptotic formula.

*Reference:* [Abel's source problem](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf).
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    let limitFormula : (ℝ → ℝ) → ℝ → ℝ := answer(sorry)
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (limitFormula f x)) := by
  sorry

/--
Existence-only version of the eventual-smoothness variant. This separates the first part of the
source problem, proving that the scaled sequence has some limit, from the stronger task of finding
an explicit expression for that limit.

*Reference:* [Abel's source problem](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf).
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth.limit_exists
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        ∃ L : ℝ,
          Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
            (𝓝 L) := by
  sorry

/--
Variant of the Bézier-Bernstein Voronovskaja problem with the required smoothness order itself
left as an answer. Replacing `(answer(sorry) : ℕ × ((ℝ → ℝ) → ℝ → ℝ))` by a concrete value lets one
state the conjecture for a chosen regularity threshold.

*Reference:* [Abel's source problem](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf).
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.answer_smoothness
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    let p : ℕ × ((ℝ → ℝ) → ℝ → ℝ) := answer(sorry)
    let m := p.1
    let limitFormula := p.2
    ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
      Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
        (𝓝 (limitFormula f x)) := by
  sorry

end VoronovskajaTypeFormula
