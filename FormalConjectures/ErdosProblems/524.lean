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
# Erdős Problem 524

*Reference:* [erdosproblems.com/524](https://www.erdosproblems.com/524)

*Paper:* P. Chojecki, "Maximum of random ±1 polynomials on [−1, 1]: a.s. order and the
lower envelope", January 30, 2026.
[ulam.ai/research/erdos524.pdf](https://www.ulam.ai/research/erdos524.pdf)

Let `t ∈ (0, 1)` have binary expansion `t = ∑_{k≥1} ε_k(t) 2^{-k}` with
`ε_k(t) ∈ {0, 1}`, and define `a_k(t) := (-1)^{ε_k(t)} ∈ {±1}`. Consider the
random algebraic polynomial
`P_n(x; t) := ∑_{k=1}^{n} a_k(t) x^k`,
and its supremum on `[-1, 1]`:
`M_n(t) := max_{x ∈ [-1, 1]} |P_n(x; t)|`.

With respect to Lebesgue measure on `(0, 1)`, the sequence `(a_k(t))_{k≥1}` is
i.i.d. Rademacher (`±1` with probability `1/2` each), so the question is
equivalently phrased on a probability space carrying i.i.d. Rademacher signs.

The original Erdős question (clarification: per [SaZy54] the supremum should
be over `x ∈ [-1, 1]` with Rademacher coefficients `±1`, not over `[0, 1]` with
binary digits `{0, 1}`) asks for the *correct order of magnitude* of `M_n(t)`.

**Solved (Chojecki, January 2026).** The almost-sure upper envelope is
`lim sup_{n → ∞} M_n(t) / √(2n log log n) = 1` a.s.,
identifying the correct upper-envelope order of magnitude as
`√(n log log n)`.

The matching *lower envelope* is settled only on a sparse subsequence
`n_m = ⌊e^{m^3}⌋`, where the minimal scale is
`M_{n_m}(t) = √(n_m) · exp(-Θ((log log n_m)^{1/3}))` infinitely often,
with explicit two-sided constants `α_-, α_+` derived from the Gao–Li–Wellner
small-deviation asymptotics for the Gaussian process
`Y(u) = ∫_0^1 e^{-us} dB(s)`. The exact constant `α_*` remains open (it would
require the exact small-ball constant for `Y`).

Extended proofs (Abel summation, two-walk sandwich, subgaussian tails, LIL
infrastructure) are available in the `add-erdos-524` branch:
https://github.com/kieranmcshane/formal-conjectures/tree/add-erdos-524
-/

open MeasureTheory ProbabilityTheory Filter Real
open scoped Topology

namespace Erdos524

/--
A sequence `a : ℕ → Ω → ℝ` is an i.i.d. Rademacher sequence if the random
variables `a k` are mutually independent and each takes values `1` and `-1`
with probability `1/2`.
-/
structure IsRademacherSequence
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) : Prop where
  /-- The random variables `(a k)` are mutually independent. -/
  indep : ProbabilityTheory.iIndepFun (fun k : ℕ => a k) ℙ
  /-- Each `a k` is a measurable function. -/
  measurable (k : ℕ) : Measurable (a k)
  /-- Each `a k` takes value `1` with probability `1/2`. -/
  prob_pos (k : ℕ) : ℙ {ω | a k ω = 1} = 1 / 2
  /-- Each `a k` takes value `-1` with probability `1/2`. -/
  prob_neg (k : ℕ) : ℙ {ω | a k ω = -1} = 1 / 2

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/--
The random algebraic polynomial of degree `n` with Rademacher coefficients
`a_1, …, a_n`:
`P_n(ω)(x) := ∑_{k=1}^{n} a_k(ω) x^k`.

Note the index range is `1 ≤ k ≤ n`, matching Chojecki's normalization
(`P_n(0) = 0`, no constant term).
-/
noncomputable def randomPoly (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, a k ω * x ^ k

/--
The supremum norm of `P_n(ω)` on the closed interval `[-1, 1]`:
`M_n(ω) := max_{x ∈ [-1, 1]} |∑_{k=1}^{n} a_k(ω) x^k|`.
-/
noncomputable def supNorm (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ x ∈ Set.Icc (-1 : ℝ) 1, |randomPoly a n ω x|

/--
The simple-random-walk partial sum `S_k(ω) := ∑_{j=1}^{k} a_j(ω) = P_k(ω)(1)`.
-/
noncomputable def walk (a : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, a j ω

/--
The signed partial sum `T_k(ω) := ∑_{j=1}^{k} (-1)^j a_j(ω) = P_k(ω)(-1)` (up
to sign). When `(a_j)` is i.i.d. Rademacher, so is `((-1)^j a_j)`, hence
`T_k` has the same law as `S_k`.
-/
noncomputable def alternatingWalk (a : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ j * a j ω

/- ### The original Erdős question -/

/--
**Erdős Problem 524.**
Determine the correct almost-sure order of magnitude of
`M_n(ω) = sup_{x ∈ [-1, 1]} |∑_{k=1}^{n} a_k(ω) x^k|`
for i.i.d. Rademacher coefficients `(a_k)`.

The phrasing in [Er61] is ambiguous; the Salem–Zygmund clarification (and the
formulation matched by Chojecki's resolution) asks for a deterministic
function `f : ℕ → ℝ` such that `M_n(ω) ≍ f(n)` almost surely (in the upper
envelope sense), and to identify `f` precisely.
-/
@[category research solved, AMS 26 60]
theorem erdos_524 :
    answer(sorry) ↔
    ∃ f : ℕ → ℝ,
      (∀ ε > 0, ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (a : ℕ → Ω → ℝ), IsRademacherSequence a →
        ∀ᵐ ω, ∀ᶠ n in atTop, supNorm a n ω ≤ (1 + ε) * f n) ∧
      (∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (a : ℕ → Ω → ℝ), IsRademacherSequence a →
        ∀ᵐ ω, ∃ᶠ n in atTop, supNorm a n ω ≥ (1 - 0.01) * f n) := by
  sorry

/- ### Chojecki (January 2026): resolution of the upper envelope -/

/--
**Theorem 6 (Chojecki 2026): sharp almost-sure upper envelope.**
Almost surely,
`lim sup_{n → ∞} M_n(ω) / √(2n log log n) = 1`.

Equivalently, the correct almost-sure upper-envelope order of magnitude of
`M_n(ω)` is `√(n log log n)`, with sharp constant `√2`.

*Proof sketch.* The lower bound `≥ 1` follows from `M_n ≥ |S_n|` (evaluate at
`x = 1`) and Kolmogorov's law of the iterated logarithm. The upper bound `≤ 1`
follows from the two-walk sandwich `M_n ≤ max(max_{k≤n} |S_k|, max_{k≤n} |T_k|)`
(Corollary 3, via Abel summation) together with Chung's maximal LIL applied
to each running maximum.
-/
@[category research solved, AMS 26 60]
theorem erdos_524.variants.sharp_upper_envelope :
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), IsRademacherSequence a →
      ∀ᵐ ω, limsup (fun n : ℕ =>
        supNorm a n ω / Real.sqrt (2 * n * Real.log (Real.log n))) atTop = 1 := by
  sorry

/--
**Proposition 4 (Chojecki 2026): subgaussian tails at the typical scale.**
There exists an absolute constant `c > 0` such that for all `n ≥ 1` and all
`u ≥ 0`, `ℙ(M_n ≥ u √n) ≤ 4 exp(-c u^2)`.

Note: the hypothesis `0 < n` is necessary because `M_0 = 0` and `u √0 = 0`,
so `ℙ(M_0 ≥ 0) = 1` which exceeds `4 exp(-c u²)` for large `u`.
-/
@[category research solved, AMS 26 60]
theorem erdos_524.variants.subgaussian_tails :
    ∃ c > 0, ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), IsRademacherSequence a →
      ∀ (n : ℕ), 0 < n → ∀ (u : ℝ), 0 ≤ u →
        (ℙ {ω | supNorm a n ω ≥ u * Real.sqrt n}).toReal ≤
          4 * Real.exp (-c * u ^ 2) := by
  sorry

/- ### The two-walk sandwich (Corollary 3, Lemma 2) -/

/--
**Lemma 2 / Corollary 3 (two-walk sandwich).** Almost surely, for every `n`,
`max(|S_n(ω)|, |T_n(ω)|) ≤ M_n(ω) ≤ max(max_{k≤n} |S_k(ω)|, max_{k≤n} |T_k(ω)|)`.

The lower bound is `M_n ≥ |P_n(±1)|`. The upper bound is obtained by Abel
summation: `P_n(x) = S_n x^n + (1 - x) ∑_{k<n} S_k x^k` for `x ∈ [0, 1]`, and
the analogous identity for `x ∈ [-1, 0]` via `b_k := (-1)^k a_k`.
-/
@[category research solved, AMS 26 60]
theorem erdos_524.variants.two_walk_sandwich :
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), IsRademacherSequence a →
      ∀ᵐ ω, ∀ (n : ℕ),
        max |walk a n ω| |alternatingWalk a n ω| ≤ supNorm a n ω ∧
        supNorm a n ω ≤
          max (⨆ k ∈ Finset.Icc 1 n, |walk a k ω|)
              (⨆ k ∈ Finset.Icc 1 n, |alternatingWalk a k ω|) := by
  sorry

/- ### Lower envelope on a sparse subsequence (Theorem 18) -/

/--
The Gao–Li–Wellner small-deviation constants `c̲ ≤ c̄` for the centered
Gaussian process `Y(u) = ∫_0^1 e^{-us} dB(s)` on `u ≥ 0`. They satisfy
`exp(-c̄ |log ε|^3) ≤ ℙ(sup_u |Y(u)| ≤ ε) ≤ exp(-c̲ |log ε|^3)`
for all sufficiently small `ε > 0`.
-/
structure GaoLiWellnerConstants where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper

/--
**Theorem 18 (Chojecki 2026): sparse-subsequence lower envelope at the
`(log log n)^{1/3}` scale.**

Let `n_m := ⌊e^{m^3}⌋`. There exist explicit constants
`α_- := (1 / (6 c̄))^{1/3}` and `α_+ := (1 / (6 c̲))^{1/3}`,
where `c̲ ≤ c̄` are the Gao–Li–Wellner small-deviation constants for the
Gaussian process `Y(u) = ∫_0^1 e^{-us} dB(s)`, such that almost surely
`α_- ≤ lim sup_{m → ∞} log(√(n_m) / M_{n_m}) / (log log n_m)^{1/3} ≤ α_+`.

Equivalently, `M_{n_m}(ω) = √(n_m) · exp(-Θ((log log n_m)^{1/3}))`
infinitely often, almost surely.
-/
@[category research solved, AMS 26 60]
theorem erdos_524.variants.sparse_lower_envelope :
    ∃ (glw : GaoLiWellnerConstants),
      let α_minus : ℝ := (1 / (6 * glw.upper)) ^ ((1 : ℝ) / 3)
      let α_plus  : ℝ := (1 / (6 * glw.lower)) ^ ((1 : ℝ) / 3)
      let n : ℕ → ℕ := fun m => ⌊Real.exp ((m : ℝ) ^ 3)⌋₊
      ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (a : ℕ → Ω → ℝ), IsRademacherSequence a →
        ∀ᵐ ω,
          α_minus ≤ limsup (fun m : ℕ =>
            Real.log (Real.sqrt (n m) / supNorm a (n m) ω) /
              (Real.log (Real.log (n m))) ^ ((1 : ℝ) / 3)) atTop ∧
          limsup (fun m : ℕ =>
            Real.log (Real.sqrt (n m) / supNorm a (n m) ω) /
              (Real.log (Real.log (n m))) ^ ((1 : ℝ) / 3)) atTop ≤ α_plus := by
  sorry

/- ### The remaining open sub-question -/

/--
**Open (Remark 19): exact constant for the lower envelope.**

The two-sided Gao–Li–Wellner bound `exp(-c̄|log ε|^3) ≤ ℙ(sup |Y| ≤ ε) ≤
exp(-c̲|log ε|^3)` would yield a single explicit constant `α_* = (6 c_*)^{-1/3}`
in an almost-sure limit theorem
`lim_{m → ∞} log(√(n_m) / M_{n_m}) / (log log n_m)^{1/3} = α_*` a.s.
*if* it could be sharpened to an exact asymptotic
`-log ℙ(sup |Y| ≤ ε) ∼ c_* |log ε|^3` as `ε ↓ 0`.

This sharpening is a major open problem in Gaussian-process small-ball theory
and is not addressed by Chojecki's resolution.

Identifying `α_*` would also require extending the sparse-subsequence
Borel–Cantelli to the full sequence `n` (a "full-sequence dependence
analysis"), which is itself nontrivial.
-/
@[category research open, AMS 26 60]
theorem erdos_524.variants.exact_lower_constant :
    answer(sorry) ↔
    ∃ α_star > 0, ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), IsRademacherSequence a →
      let n : ℕ → ℕ := fun m => ⌊Real.exp ((m : ℝ) ^ 3)⌋₊
      ∀ᵐ ω, Tendsto (fun m : ℕ =>
        Real.log (Real.sqrt (n m) / supNorm a (n m) ω) /
          (Real.log (Real.log (n m))) ^ ((1 : ℝ) / 3)) atTop (𝓝 α_star) := by
  sorry

end Erdos524
