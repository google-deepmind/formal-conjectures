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
lower envelope", January 30, 2026. [ulam.ai/research/erdos524.pdf](https://www.ulam.ai/research/erdos524.pdf)

Let `t ∈ (0, 1)` have binary expansion `t = ∑_{k≥1} ε_k(t) 2^{-k}` with
`ε_k(t) ∈ {0, 1}`, and define `a_k(t) := (-1)^{ε_k(t)} ∈ {±1}`. Consider the
random algebraic polynomial
`P_n(x; t) := ∑_{k=1}^{n} a_k(t) x^k`,
and its supremum on `[-1, 1]`:
`M_n(t) := max_{x ∈ [-1, 1]} |P_n(x; t)|`.

With respect to Lebesgue measure on `(0, 1)`, the sequence `(a_k(t))_{k≥1}` is
i.i.d. Rademacher (`±1` with probability `1/2` each), so the question is
equivalently phrased on a probability space carrying i.i.d. Rademacher signs.

The original Erdős question (clarification: per [Sa-Zy54] the supremum should
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

section Helpers
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

set_option linter.unusedSectionVars false in
/-- Evaluating at `x = 1` gives the simple random walk `S_n`. -/
private theorem randomPoly_at_one (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    randomPoly a n ω 1 = walk a n ω := by
  simp [randomPoly, walk, one_pow, mul_one]

set_option linter.unusedSectionVars false in
/-- Evaluating at `x = -1` gives the alternating walk `T_n`. -/
private theorem randomPoly_at_neg_one (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    randomPoly a n ω (-1) = alternatingWalk a n ω := by
  simp [randomPoly, alternatingWalk, mul_comm]

set_option linter.unusedSectionVars false in
/-- `|P_n(ω)(x)| ≤ supNorm a n ω` for any `x ∈ [-1, 1]`. -/
private theorem abs_randomPoly_le_supNorm (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |randomPoly a n ω x| ≤ supNorm a n ω := by
  unfold supNorm
  -- Step 1: outer le_ciSup_of_le at y = x
  have hbdd_outer : BddAbove (Set.range fun y =>
      ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |randomPoly a n ω y|) := by
    refine ⟨∑ k ∈ Finset.Icc 1 n, |a k ω|, ?_⟩
    rintro z ⟨y, rfl⟩
    rcases em (y ∈ Set.Icc (-1 : ℝ) 1) with hy | hy
    · haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy⟩
      exact ciSup_le fun _ => by
        simp only [randomPoly]
        calc |∑ k ∈ Finset.Icc 1 n, a k ω * y ^ k|
            ≤ ∑ k ∈ Finset.Icc 1 n, |a k ω * y ^ k| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k ∈ Finset.Icc 1 n, |a k ω| * |y ^ k| := by
              congr 1; ext k; exact abs_mul _ _
          _ ≤ ∑ k ∈ Finset.Icc 1 n, |a k ω| * 1 := by
              gcongr with k _
              rw [abs_pow]
              exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith [hy.1], hy.2⟩)
          _ = ∑ k ∈ Finset.Icc 1 n, |a k ω| := by simp
    · -- y ∉ [-1, 1]: inner iSup is sSup of empty range ≤ bound
      have : (⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |randomPoly a n ω y|) ≤ 0 := by
        have hempty : (Set.range fun (_ : y ∈ Set.Icc (-1 : ℝ) 1) =>
            |randomPoly a n ω y|) = ∅ := Set.range_eq_empty_iff.mpr ⟨hy⟩
        simp [iSup, hempty]
      linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.Icc 1 n) => abs_nonneg (a k ω))]
  calc |randomPoly a n ω x|
      ≤ ⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1), |randomPoly a n ω x| :=
        le_ciSup ⟨_, Set.forall_mem_range.mpr fun _ => le_rfl⟩ hx
    _ ≤ ⨆ y ∈ Set.Icc (-1 : ℝ) 1, |randomPoly a n ω y| :=
        le_ciSup hbdd_outer x

set_option linter.unusedSectionVars false in
/-- `|S_n(ω)| ≤ M_n(ω)`: the walk is bounded by the sup norm. -/
private theorem walk_le_supNorm (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    |walk a n ω| ≤ supNorm a n ω := by
  rw [← randomPoly_at_one]
  exact abs_randomPoly_le_supNorm a n ω (Set.right_mem_Icc.mpr (by norm_num))

set_option linter.unusedSectionVars false in
/-- `|T_n(ω)| ≤ M_n(ω)`: the alternating walk is bounded by the sup norm. -/
private theorem alternatingWalk_le_supNorm (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    |alternatingWalk a n ω| ≤ supNorm a n ω := by
  rw [← randomPoly_at_neg_one]
  exact abs_randomPoly_le_supNorm a n ω (Set.left_mem_Icc.mpr (by norm_num))

/- #### Abel summation helpers -/

set_option linter.unusedSectionVars false in
private lemma walk_zero (a : ℕ → Ω → ℝ) (ω : Ω) : walk a 0 ω = 0 := by
  unfold walk; simp

set_option linter.unusedSectionVars false in
private lemma randomPoly_succ (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) :
    randomPoly a (n + 1) ω x = randomPoly a n ω x + a (n + 1) ω * x ^ (n + 1) := by
  simp only [randomPoly]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

set_option linter.unusedSectionVars false in
private lemma walk_succ (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    walk a (n + 1) ω = walk a n ω + a (n + 1) ω := by
  simp only [walk]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

set_option linter.unusedSectionVars false in
/-- **Abel summation identity.** For `x ∈ ℝ`:
`P_n(x) = S_n · x^n + (1 - x) · ∑_{k=1}^{n-1} S_k · x^k`. -/
private theorem abel_identity (a : ℕ → Ω → ℝ) (ω : Ω) :
    ∀ n : ℕ, ∀ x : ℝ,
      randomPoly a n ω x =
        walk a n ω * x ^ n +
          (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), walk a k ω * x ^ k := by
  intro n
  induction n with
  | zero =>
    intro x
    simp [randomPoly, walk_zero]
  | succ n ih =>
    intro x
    rw [randomPoly_succ, ih]
    -- Goal: ... + a(n+1) x^{n+1} = walk(n+1) x^{n+1} + (1-x) ∑_{k=1}^{n} walk(k) x^k
    rw [walk_succ]
    by_cases hn : n = 0
    · subst hn; simp [walk_zero]
    · -- Split ∑ k ∈ Icc 1 n = ∑ k ∈ Icc 1 (n-1) + f(n)
      have hsplit : ∀ f : ℕ → ℝ, ∑ k ∈ Finset.Icc 1 n, f k =
          (∑ k ∈ Finset.Icc 1 (n - 1), f k) + f n := by
        intro f
        have h1 : Finset.Icc 1 n = Finset.Icc 1 (n - 1) ∪ {n} := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
        have h2 : Disjoint (Finset.Icc 1 (n - 1)) {n} := by
          simp only [Finset.disjoint_singleton_right, Finset.mem_Icc]; omega
        rw [h1, Finset.sum_union h2, Finset.sum_singleton]
      rw [show n + 1 - 1 = n from by omega, hsplit]
      ring

/-- The Abel weights `x^n + (1-x) ∑_{k=1}^{n-1} x^k` equal `x` for `n ≥ 1`. -/
private theorem weight_eq (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    x ^ n + (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), x ^ k = x := by
  -- Distribute (1-x) and telescope: ∑ (x^k - x^{k+1}) = x - x^n
  have hdist : (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), x ^ k =
      ∑ k ∈ Finset.Icc 1 (n - 1), (x ^ k - x ^ (k + 1)) := by
    rw [Finset.mul_sum]; congr 1; ext k; ring
  rw [hdist]
  induction n with
  | zero => omega
  | succ m ihm =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [show m + 1 - 1 = m from by omega]
      have hsplit : Finset.Icc 1 m = Finset.Icc 1 (m - 1) ∪ {m} := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
      have hdisj : Disjoint (Finset.Icc 1 (m - 1)) {m} := by
        simp only [Finset.disjoint_singleton_right, Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_union hdisj, Finset.sum_singleton]
      have hdist_m : (1 - x) * ∑ k ∈ Finset.Icc 1 (m - 1), x ^ k =
          ∑ k ∈ Finset.Icc 1 (m - 1), (x ^ k - x ^ (k + 1)) := by
        rw [Finset.mul_sum]; congr 1; ext k; ring
      have := ihm hm hdist_m
      linarith

set_option linter.unusedSectionVars false in
/-- Abel bound: for `x ∈ [0, 1]`, `|P_n(x)| ≤ M` whenever `M ≥ 0` and `|S_k| ≤ M` for
all `k ∈ {1, …, n}`. -/
private theorem abel_bound_nonneg (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ k ∈ Finset.Icc 1 n, |walk a k ω| ≤ M) :
    |randomPoly a n ω x| ≤ M := by
  rw [abel_identity a ω n x]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [walk_zero]; exact hM0
  · -- n ≥ 1: bound |S_n x^n + (1-x) ∑ S_k x^k| ≤ M
    have h1x : 0 ≤ 1 - x := by linarith
    -- Triangle inequality + nonneg weights
    have key : |walk a n ω * x ^ n +
        (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), walk a k ω * x ^ k| ≤
        |walk a n ω| * x ^ n +
        (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), |walk a k ω| * x ^ k := by
      calc _ ≤ |walk a n ω * x ^ n| +
              |(1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), walk a k ω * x ^ k| :=
            abs_add_le _ _
        _ = |walk a n ω| * x ^ n +
              (1 - x) * |∑ k ∈ Finset.Icc 1 (n - 1), walk a k ω * x ^ k| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hx0 n), abs_of_nonneg h1x]
        _ ≤ |walk a n ω| * x ^ n +
              (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), |walk a k ω * x ^ k| := by
            gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
            congr 1; congr 1
            apply Finset.sum_congr rfl; intro k _
            rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 k)]
    -- Bound each |S_k| ≤ M
    have bound : |walk a n ω| * x ^ n +
        (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), |walk a k ω| * x ^ k ≤
        M * x ^ n + (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), M * x ^ k := by
      gcongr with k hk
      · exact hM n (Finset.mem_Icc.mpr ⟨hn, le_refl n⟩)
      · exact hM k (Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 (Nat.sub_le n 1)⟩)
    -- Factor out M and use weight ≤ 1
    calc _ ≤ |walk a n ω| * x ^ n +
          (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), |walk a k ω| * x ^ k := key
      _ ≤ M * x ^ n + (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), M * x ^ k := bound
      _ = M * (x ^ n + (1 - x) * ∑ k ∈ Finset.Icc 1 (n - 1), x ^ k) := by
          simp_rw [← Finset.mul_sum]; ring
      _ ≤ M * 1 := by
          gcongr; rw [weight_eq n hn x]; exact hx1
      _ = M := mul_one M

set_option linter.unusedSectionVars false in
/-- If `|P_n(x)| ≤ M` for all `x ∈ [-1, 1]` and `M ≥ 0`, then `supNorm ≤ M`. -/
private theorem supNorm_le (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |randomPoly a n ω x| ≤ M) :
    supNorm a n ω ≤ M := by
  unfold supNorm
  apply ciSup_le
  intro y
  rcases em (y ∈ Set.Icc (-1 : ℝ) 1) with hy | hy
  · haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy⟩
    exact ciSup_le fun _ => hM y hy
  · have : (⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |randomPoly a n ω y|) ≤ 0 := by
      have hempty : (Set.range fun (_ : y ∈ Set.Icc (-1 : ℝ) 1) =>
          |randomPoly a n ω y|) = ∅ := Set.range_eq_empty_iff.mpr ⟨hy⟩
      simp [iSup, hempty]
    linarith

set_option linter.unusedSectionVars false in
/-- `P_n(-y) = ∑ (-1)^k a_k y^k` — evaluating at `-y` swaps sign pattern. -/
private theorem randomPoly_neg (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (y : ℝ) :
    randomPoly a n ω (-y) =
      randomPoly (fun j ω => (-1 : ℝ) ^ j * a j ω) n ω y := by
  simp only [randomPoly]
  apply Finset.sum_congr rfl; intro k _; ring

set_option linter.unusedSectionVars false in
/-- The walk of `(-1)^j a_j` equals the alternating walk. -/
private theorem walk_neg_eq_alternatingWalk (a : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    walk (fun j ω => (-1 : ℝ) ^ j * a j ω) k ω = alternatingWalk a k ω := by
  simp [walk, alternatingWalk]

set_option linter.unusedSectionVars false in
/-- If `(a_k)` is i.i.d. Rademacher, so is `((-1)^k · a_k)`. Multiplying by `±1` permutes
`{-1, 1}` and preserves independence. -/
private theorem isRademacherSequence_neg_mul
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) :
    IsRademacherSequence (fun j ω => (-1 : ℝ) ^ j * a j ω) where
  indep := by
    -- (-1)^j * a_j = (fun x => (-1)^j * x) ∘ a_j, independence preserved under det. maps
    have := ha.indep.comp (fun j => (fun x : ℝ => (-1 : ℝ) ^ j * x))
      (fun j => by exact measurable_const_mul _)
    exact this
  measurable k := by exact (measurable_const.mul (ha.measurable k))
  prob_pos k := by
    rcases Nat.even_or_odd k with hk | hk
    · simp only [hk.neg_one_pow, one_mul]; exact ha.prob_pos k
    · have hset : {ω | (-1 : ℝ) ^ k * a k ω = 1} = {ω | a k ω = -1} := by
        ext ω; simp [hk.neg_one_pow]; constructor <;> intro h <;> linarith
      rw [hset]; exact ha.prob_neg k
  prob_neg k := by
    rcases Nat.even_or_odd k with hk | hk
    · simp only [hk.neg_one_pow, one_mul]; exact ha.prob_neg k
    · have hset : {ω | (-1 : ℝ) ^ k * a k ω = -1} = {ω | a k ω = 1} := by
        ext ω; simp [hk.neg_one_pow]
      rw [hset]; exact ha.prob_pos k

end Helpers

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
  -- TODO: meta-theorem wrapping sharp_upper_envelope + sparse_lower_envelope.
  -- Cannot be discharged until both components are proven.
  sorry

/- ### Chojecki (January 2026): resolution of the upper envelope -/

/--
**Theorem 6 (Chojecki 2026): sharp almost-sure upper envelope.**
Almost surely,
`lim sup_{n → ∞} M_n(ω) / √(2n log log n) = 1`.

Equivalently, the correct almost-sure upper-envelope order of magnitude of
`M_n(ω)` is `√(n log log n)`, with sharp constant `√2`.

*Proof.* The lower bound `≥ 1` follows from `M_n ≥ |S_n|` (evaluate at `x = 1`)
and Kolmogorov's law of the iterated logarithm. The upper bound `≤ 1` follows
from the two-walk sandwich `M_n ≤ max(max_{k≤n} |S_k|, max_{k≤n} |T_k|)`
(Corollary 3, via Abel summation) together with Chung's maximal LIL applied
to each running maximum.
-/
@[category research solved, AMS 26 60]
theorem erdos_524.variants.sharp_upper_envelope :
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), IsRademacherSequence a →
      ∀ᵐ ω, limsup (fun n : ℕ =>
        supNorm a n ω / Real.sqrt (2 * n * Real.log (Real.log n))) atTop = 1 := by
  -- TODO: requires Kolmogorov's law of the iterated logarithm (for the ≥ 1 direction via
  -- M_n ≥ |S_n| and walk_le_supNorm) and Chung's maximal LIL (for the ≤ 1 direction via
  -- two_walk_sandwich upper bound). Neither is in Mathlib v4.27.0 in usable form.
  -- Kolmogorov LIL: no Mathlib PR known as of 2026-01.
  -- Chung's maximal LIL: not in Mathlib; would require Chung's liminf law for running max.
  sorry

/- #### Probability infrastructure for subgaussian tails -/

-- Rademacher variables take values ±1 a.e.
set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
set_option linter.unusedSectionVars false in
private lemma rademacher_ae_mem_pm_one (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (k : ℕ) :
    ∀ᵐ ω, a k ω = 1 ∨ a k ω = -1 := by
  rw [ae_iff]
  have h1 := ha.prob_pos k
  have h2 := ha.prob_neg k
  have hm := ha.measurable k
  have hms1 : MeasurableSet {ω | a k ω = 1} := hm (measurableSet_singleton 1)
  have hms2 : MeasurableSet {ω | a k ω = -1} := hm (measurableSet_singleton (-1))
  have hdisj : Disjoint {ω | a k ω = 1} {ω | a k ω = -1} := by
    rw [Set.disjoint_left]; intro ω h1' h2'; simp at h1' h2'; linarith
  have hunion : ℙ ({ω | a k ω = 1} ∪ {ω | a k ω = -1}) = 1 := by
    rw [measure_union hdisj hms2, h1, h2, ENNReal.div_add_div_same, one_add_one_eq_two,
      ENNReal.div_self (by norm_num) (by norm_num)]
  have hcompl : ℙ (({ω | a k ω = 1} ∪ {ω | a k ω = -1})ᶜ) = 0 := by
    rw [measure_compl (hms1.union hms2) (measure_ne_top _ _), hunion]; simp
  exact le_antisymm (le_trans (measure_mono (fun ω hω => by
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hω ⊢; exact hω))
    (le_of_eq hcompl)) (zero_le _)

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
set_option linter.unusedSectionVars false in
/-- Each Rademacher variable `a k` is identically distributed with its negation `-(a k)`. -/
private theorem identDistrib_neg_rademacher (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (k : ℕ) :
    IdentDistrib (a k) (fun ω => -(a k ω)) ℙ ℙ := by
  classical
  refine ⟨(ha.measurable k).aemeasurable, (measurable_neg.comp (ha.measurable k)).aemeasurable, ?_⟩
  have hae := rademacher_ae_mem_pm_one a ha k
  have rp : ∀ T : Set ℝ, MeasurableSet T →
      ℙ (a k ⁻¹' T) = (if (1 : ℝ) ∈ T then 1 / 2 else 0) +
        (if (-1 : ℝ) ∈ T then 1 / 2 else 0) := by
    intro T _
    rcases em ((1 : ℝ) ∈ T) with h1 | h1 <;> rcases em ((-1 : ℝ) ∈ T) with hm1 | hm1
    · rw [if_pos h1, if_pos hm1, measure_congr (show a k ⁻¹' T =ᵐ[ℙ] Set.univ from by
        filter_upwards [hae] with ω hω; show ((a k ω ∈ T) = True)
        rcases hω with hω | hω <;> simp [hω, h1, hm1]), measure_univ,
        ENNReal.div_add_div_same, one_add_one_eq_two,
        ENNReal.div_self (by norm_num) (by norm_num)]
    · rw [if_pos h1, if_neg hm1, add_zero, measure_congr (show a k ⁻¹' T =ᵐ[ℙ] {ω | a k ω = 1}
        from by
        filter_upwards [hae] with ω hω
        show ((a k ω ∈ T) = (a k ω = 1))
        rcases hω with hω | hω <;> (simp [hω, h1, hm1]; try norm_num)), ha.prob_pos k]
    · rw [if_neg h1, if_pos hm1, zero_add, measure_congr (show a k ⁻¹' T =ᵐ[ℙ] {ω | a k ω = -1}
        from by
        filter_upwards [hae] with ω hω
        show ((a k ω ∈ T) = (a k ω = -1))
        rcases hω with hω | hω <;> (simp [hω, h1, hm1]; try norm_num)), ha.prob_neg k]
    · rw [if_neg h1, if_neg hm1, measure_congr (show a k ⁻¹' T =ᵐ[ℙ] (∅ : Set Ω) from by
        filter_upwards [hae] with ω hω; show ((a k ω ∈ T) = False)
        rcases hω with hω | hω <;> simp [hω, h1, hm1]), measure_empty, add_zero]
  ext s hs
  rw [Measure.map_apply (ha.measurable k) hs,
      show (fun ω => -(a k ω)) = Neg.neg ∘ a k from rfl,
      ← Measure.map_map measurable_neg (ha.measurable k),
      Measure.map_apply measurable_neg hs,
      Measure.map_apply (ha.measurable k) (measurable_neg hs),
      rp s hs, rp (Neg.neg ⁻¹' s) (measurable_neg hs)]
  simp only [Set.mem_preimage, neg_neg]; ring

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
set_option linter.unusedSectionVars false in
/-- The integral of a Rademacher variable is zero. -/
private theorem integral_rademacher_eq_zero (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (k : ℕ) :
    ∫ ω, a k ω ∂ℙ = 0 := by
  have h := (identDistrib_neg_rademacher a ha k).integral_eq
  simp only [integral_neg] at h; linarith

-- Symmetry of Rademacher walk: ℙ(S_m ≥ 0) ≥ 1/2.
-- Proof: -S_m has the same distribution as S_m (since -a_k ~d a_k).
-- So ℙ(S_m ≥ 0) = ℙ(-S_m ≥ 0) = ℙ(S_m ≤ 0).
-- And ℙ(S_m ≥ 0) + ℙ(S_m ≤ 0) ≥ 1, hence ℙ(S_m ≥ 0) ≥ 1/2.
set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
set_option linter.unusedSectionVars false in
private lemma rademacher_walk_nonneg_prob (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (m : ℕ) :
    (1 : ℝ) / 2 ≤ (ℙ {ω | walk a m ω ≥ 0}).toReal := by
  -- Step 1: neg_a is also Rademacher
  let neg_a : ℕ → Ω → ℝ := fun j ω => -(a j ω)
  have hna : IsRademacherSequence neg_a := by
    refine ⟨ha.indep.comp (β := fun _ => ℝ) (fun _ => Neg.neg) (fun _ => measurable_neg),
      fun k => measurable_neg.comp (ha.measurable k), fun k => ?_, fun k => ?_⟩
    · convert ha.prob_neg k using 2; ext ω; simp [neg_a]; constructor <;> intro h <;> linarith
    · convert ha.prob_pos k using 2; ext ω; simp [neg_a]
  have hwn : ∀ ω, walk neg_a m ω = -(walk a m ω) := fun ω => by
    simp [walk, neg_a, Finset.sum_neg_distrib]
  -- Step 2: each a k and neg_a k are identically distributed (Rademacher symmetry)
  -- Helper: ℙ(a k ⁻¹' T) for any measurable T, using ae support on {±1}
  open scoped Classical in
  have rademacher_preimage : ∀ k, ∀ T : Set ℝ, MeasurableSet T →
      ℙ (a k ⁻¹' T) = (if (1 : ℝ) ∈ T then 1 / 2 else 0) +
        (if (-1 : ℝ) ∈ T then 1 / 2 else 0) := by
    intro k T _
    have hae := rademacher_ae_mem_pm_one a ha k
    rcases em ((1 : ℝ) ∈ T) with h1 | h1 <;> rcases em ((-1 : ℝ) ∈ T) with hm1 | hm1
    · -- 1 ∈ T, -1 ∈ T: preimage is a.e. univ, measure = 1 = 1/2 + 1/2
      rw [if_pos h1, if_pos hm1, measure_congr (show a k ⁻¹' T =ᵐ[ℙ] Set.univ from by
        filter_upwards [hae] with ω hω
        show ((a k ω ∈ T) = True)
        rcases hω with hω | hω <;> simp [hω, h1, hm1]), measure_univ,
        ENNReal.div_add_div_same, one_add_one_eq_two,
        ENNReal.div_self (by norm_num) (by norm_num)]
    · rw [if_pos h1, if_neg hm1, add_zero, measure_congr (show a k ⁻¹' T =ᵐ[ℙ] {ω | a k ω = 1}
        from by
        filter_upwards [hae] with ω hω
        show ((a k ω ∈ T) = (a k ω = 1))
        rcases hω with hω | hω <;> (simp [hω, h1, hm1]; try norm_num)), ha.prob_pos k]
    · rw [if_neg h1, if_pos hm1, zero_add, measure_congr (show a k ⁻¹' T =ᵐ[ℙ] {ω | a k ω = -1}
        from by
        filter_upwards [hae] with ω hω
        show ((a k ω ∈ T) = (a k ω = -1))
        rcases hω with hω | hω <;> (simp [hω, h1, hm1]; try norm_num)), ha.prob_neg k]
    · rw [if_neg h1, if_neg hm1, measure_congr (show a k ⁻¹' T =ᵐ[ℙ] (∅ : Set Ω) from by
        filter_upwards [hae] with ω hω
        show ((a k ω ∈ T) = False)
        rcases hω with hω | hω <;> simp [hω, h1, hm1]), measure_empty, add_zero]
  have hid : ∀ k, IdentDistrib (a k) (neg_a k) ℙ ℙ := by
    intro k
    refine ⟨(ha.measurable k).aemeasurable, (hna.measurable k).aemeasurable, ?_⟩
    ext s hs
    simp only [Measure.map_apply (ha.measurable k) hs,
      Measure.map_apply (hna.measurable k) hs]
    -- neg_a k ⁻¹' s = a k ⁻¹' (Neg.neg ⁻¹' s)
    change ℙ (a k ⁻¹' s) = ℙ (a k ⁻¹' {x | -x ∈ s})
    rw [rademacher_preimage k s hs,
        rademacher_preimage k {x | -x ∈ s} (measurable_neg hs)]
    -- LHS has (if 1∈s ...) + (if -1∈s ...), RHS has (if -1∈s ...) + (if 1∈s ...)
    simp only [Set.mem_setOf_eq, neg_neg]; ring
  -- Step 3: joint IdentDistrib via IdentDistrib.pi (finite-dimensional distributions)
  have hpi := IdentDistrib.pi hid ha.indep hna.indep
  -- Step 4: compose with Finset.sum to get walk IdentDistrib
  have hsum_meas : Measurable (fun f : ℕ → ℝ => ∑ j ∈ Finset.Icc 1 m, f j) :=
    Finset.measurable_sum _ fun j _ => measurable_pi_apply j
  have hwalk_id : IdentDistrib (walk a m) (walk neg_a m) ℙ ℙ := hpi.comp hsum_meas
  -- Step 5: ℙ({walk ≥ 0}) = ℙ({walk ≤ 0}) via distributional symmetry
  have hprob_eq : ℙ {ω | walk a m ω ≥ 0} = ℙ {ω | walk a m ω ≤ 0} := by
    have h := hwalk_id.measure_mem_eq (s := Set.Ici 0) measurableSet_Ici
    simp only [Set.preimage, Set.Ici, Set.mem_setOf_eq] at h
    rw [h]; congr 1; ext ω; simp only [Set.mem_setOf_eq, hwn ω]; constructor <;> intro h <;> linarith
  -- Step 6: {walk ≥ 0} ∪ {walk ≤ 0} = univ, so ℙ ≥ 1, hence each ≥ 1/2
  have hcov : {ω : Ω | walk a m ω ≥ 0} ∪ {ω | walk a m ω ≤ 0} = Set.univ := by
    ext ω; simp; exact (le_total (walk a m ω) 0).symm
  have hge : 1 ≤ 2 * ℙ {ω : Ω | walk a m ω ≥ 0} := by
    calc (1 : ENNReal) = ℙ (Set.univ : Set Ω) := measure_univ.symm
      _ = ℙ ({ω | walk a m ω ≥ 0} ∪ {ω | walk a m ω ≤ 0}) := by rw [hcov]
      _ ≤ ℙ {ω | walk a m ω ≥ 0} + ℙ {ω | walk a m ω ≤ 0} := measure_union_le _ _
      _ = ℙ {ω | walk a m ω ≥ 0} + ℙ {ω | walk a m ω ≥ 0} := by rw [hprob_eq]
      _ = 2 * ℙ {ω | walk a m ω ≥ 0} := (two_mul _).symm
  -- Convert from ENNReal to ℝ: 1 ≤ 2 * ℙ(S) implies (ℙ S).toReal ≥ 1/2
  have hfin : ℙ {ω : Ω | walk a m ω ≥ 0} ≠ ⊤ := measure_ne_top _ _
  have h2fin : 2 * ℙ {ω : Ω | walk a m ω ≥ 0} ≠ ⊤ := by
    rw [two_mul]; exact ENNReal.add_ne_top.mpr ⟨hfin, hfin⟩
  have hreal : 1 ≤ 2 * (ℙ {ω : Ω | walk a m ω ≥ 0}).toReal := by
    have h1 : (1 : ℝ) ≤ (2 * ℙ {ω | walk a m ω ≥ 0}).toReal := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono h2fin hge
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h1
  linarith

-- Note: Lévy's maximal inequality (ℙ(max S_k ≥ t) ≤ 2ℙ(S_n ≥ t)) is not needed here
-- since one_sided_running_max gives the stronger exp(-t²/(2n)) bound via Doob's inequality.

-- Running-max tail bound: ℙ(max_{k≤n} |S_k| ≥ u√n) ≤ 2 exp(-u²/2).
-- Proof route: Doob's maximal inequality (MeasureTheory.maximal_ineq) applied to the
-- nonneg submartingale exp(λ·S_k), combined with the MGF bound E[exp(λ·S_n)] ≤ exp(λ²n/2)
-- from Hoeffding's lemma (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero).
-- Specifically:
--   P(max_k S_k ≥ a) ≤ E[exp(λ S_n)] / exp(λa) ≤ exp(λ²n/2 - λa)
--   Optimize λ = a/n: P(max_k S_k ≥ a) ≤ exp(-a²/(2n)).
--   Two-sided: P(max_k |S_k| ≥ a) ≤ 2 exp(-a²/(2n)).
-- The submartingale property of exp(λ·S_k) requires:
--   (1) building the natural filtration for (a_k),
--   (2) proving adaptedness + integrability,
--   (3) E[exp(λ·a_{k+1}) | F_k] = cosh(λ) ≥ 1 (via independence + Hoeffding's lemma).
-- Infrastructure needed: natural filtration, conditional independence → conditional MGF.
set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
-- One-sided running-max bound: the core sorry requiring submartingale infrastructure.
-- Proof route: Doob's maximal_ineq on exp(λ·walk a k) submartingale with Filtration.natural.
-- Key Mathlib infrastructure available:
--   • Filtration.natural (Probability.Process.Filtration)
--   • iIndepFun.condExp_natural_ae_eq_of_lt (Probability.BorelCantelli)
--   • MeasureTheory.maximal_ineq (Probability.Martingale.OptionalStopping)
set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private theorem one_sided_running_max
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t) :
    (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t}).toReal ≤
      Real.exp (-t ^ 2 / (2 * n)) := by
  -- Proof by Doob's maximal inequality on the exponential submartingale exp(λ · S_k).
  -- Natural filtration
  let hm : ∀ k, StronglyMeasurable (a k) := fun k => (ha.measurable k).stronglyMeasurable
  let ℱ := Filtration.natural (fun k => a k) hm
  -- Exponential submartingale: f k ω = exp((t/n) · walk a k ω)
  set lam : ℝ := t / n with hlam_def
  set f : ℕ → Ω → ℝ := fun k ω => Real.exp (lam * walk a k ω) with hf_def
  -- Step 1: f is a nonneg submartingale w.r.t. ℱ
  -- Extract adapted and integrable proofs so submg can reference them
  have hadapted : StronglyAdapted ℱ f := by
    intro k
    have hwalk_sm : StronglyMeasurable[ℱ k] (walk a k) := by
      have : StronglyMeasurable[ℱ k] (∑ j ∈ Finset.Icc 1 k, fun ω => a j ω) :=
        Finset.stronglyMeasurable_sum _ fun j hj =>
          (Filtration.stronglyAdapted_natural hm j).mono
            (ℱ.mono (Finset.mem_Icc.mp hj).2)
      convert this using 1; ext ω; simp [walk]
    exact continuous_exp.comp_stronglyMeasurable (hwalk_sm.const_mul lam)
  have hae_icc : ∀ j, ∀ᵐ ω, a j ω ∈ Set.Icc (-1 : ℝ) 1 := by
    intro j; filter_upwards [rademacher_ae_mem_pm_one a ha j] with ω hω
    rcases hω with h | h <;> simp [h]
  have hintegrable : ∀ k, Integrable (f k) ℙ := by
    intro k
    have hconv : f k = fun ω => Real.exp (lam * (∑ j ∈ Finset.Icc 1 k, a j) ω) := by
      ext ω; simp [hf_def, walk, Finset.sum_apply]
    rw [hconv]
    exact ha.indep.integrable_exp_mul_sum (fun j => ha.measurable j)
      (fun j _ => integrable_exp_mul_of_mem_Icc (ha.measurable j).aemeasurable (hae_icc j))
  have hsubmg : ∀ i, f i ≤ᵐ[ℙ] ℙ[f (i + 1) | ℱ i] := by
    intro i
    -- f(i+1) ω = f(i) ω * exp(lam * a(i+1) ω) by walk_succ + exp_add
    set g : Ω → ℝ := fun ω => Real.exp (lam * a (i + 1) ω) with hg_def
    have hfg : f (i + 1) = f i * g := by
      ext ω; simp only [hf_def, Pi.mul_apply, hg_def, walk_succ]; rw [mul_add, Real.exp_add]
    -- g is integrable (exp of bounded Rademacher)
    have hg_int : Integrable g ℙ :=
      integrable_exp_mul_of_mem_Icc (ha.measurable (i + 1)).aemeasurable (hae_icc (i + 1))
    -- Pullout: μ[f_i * g | ℱ_i] =ᵐ f_i * μ[g | ℱ_i]
    have hpull := condExp_mul_of_aestronglyMeasurable_left
      (hadapted i).aestronglyMeasurable (hfg ▸ hintegrable (i + 1)) hg_int
    -- Independence: μ[g | ℱ_i] =ᵐ fun _ => ∫ ω, g ω ∂ℙ
    -- g = (exp ∘ (lam * ·)) ∘ a(i+1) is comap(a(i+1))-measurable, independent of ℱ_i
    have hg_cond : ℙ[g | ℱ i] =ᵐ[ℙ] fun _ => ∫ ω, g ω ∂ℙ :=
      condExp_indep_eq (ha.measurable (i + 1)).comap_le (Filtration.le ℱ i)
        (((continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
          (comap_measurable (a (i + 1)))).stronglyMeasurable)
        (ha.indep.indep_comap_natural_of_lt hm (Nat.lt_succ_of_le le_rfl))
    -- E[g] = E[exp(lam * a_{i+1})] ≥ 1 via exp(x) ≥ 1+x and E[a] = 0
    have hint_a : Integrable (a (i + 1)) ℙ := (integrable_const (1 : ℝ)).mono'
      (ha.measurable (i + 1)).aestronglyMeasurable
      (by filter_upwards [rademacher_ae_mem_pm_one a ha (i + 1)] with ω hω
          rcases hω with h | h <;> simp [h])
    have hcosh : 1 ≤ ∫ ω, g ω ∂ℙ := by
      calc (1 : ℝ) = 1 + lam * 0 := by ring
        _ = 1 + lam * ∫ ω, a (i + 1) ω ∂ℙ := by
            rw [integral_rademacher_eq_zero a ha (i + 1)]
        _ = ∫ ω, (1 + lam * a (i + 1) ω) ∂ℙ := by
            rw [integral_add (integrable_const 1) (hint_a.const_mul lam), integral_const_mul]
            simp [integral_const, probReal_univ]
        _ ≤ ∫ ω, g ω ∂ℙ := by
            apply integral_mono_ae ((integrable_const 1).add (hint_a.const_mul lam)) hg_int
            filter_upwards with ω
            show 1 + lam * a (i + 1) ω ≤ g ω
            simp only [hg_def]; linarith [add_one_le_exp (lam * a (i + 1) ω)]
    -- Combine: f_i ≤ f_i * E[g] =ᵐ f_i * μ[g|ℱ_i] =ᵐ μ[f_i*g|ℱ_i] = μ[f(i+1)|ℱ_i]
    rw [hfg]
    calc f i ≤ᵐ[ℙ] fun ω => f i ω * ∫ ω', g ω' ∂ℙ := by
          filter_upwards with ω
          exact le_mul_of_one_le_right (le_of_lt (Real.exp_pos _)) hcosh
      _ =ᵐ[ℙ] fun ω => f i ω * (ℙ[g | ℱ i]) ω := by
          filter_upwards [hg_cond] with ω hω; simp only [hω]
      _ =ᵐ[ℙ] ℙ[f i * g | ℱ i] := hpull.symm
  have hsub : Submartingale f ℱ ℙ := submartingale_nat hadapted hintegrable hsubmg
  have hnn : 0 ≤ f := fun k ω => le_of_lt (Real.exp_pos _)
  -- Step 2: Doob's maximal inequality gives ℙ(∃k, walk k ≥ t) ≤ E[f_n] / exp(λt).
  -- Uses maximal_ineq with ε = exp(λt) on the nonneg submartingale f, plus set
  -- conversion between Icc 1 n and range (n+1), and exp monotonicity.
  have hdobo : (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t}).toReal ≤
      (∫ ω, f n ω ∂ℙ) / Real.exp (lam * t) := by
    -- Set containment: {walk ≥ t} ⊆ {sup' f ≥ exp(lam*t)} via exp monotonicity
    set ε : NNReal := ⟨Real.exp (lam * t), le_of_lt (Real.exp_pos _)⟩
    set A := {ω : Ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one fun k => f k ω} with hA_def
    have hlam_nn : 0 ≤ lam := div_nonneg ht (Nat.cast_nonneg n)
    have hcontain : {ω : Ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t} ⊆ A := by
      intro ω ⟨j, hj, hwj⟩
      show (ε : ℝ) ≤ _
      have hj_range : j ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hj).2; omega)
      calc (ε : ℝ) = Real.exp (lam * t) := rfl
        _ ≤ Real.exp (lam * walk a j ω) :=
            Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left hwj hlam_nn)
        _ = f j ω := by simp [hf_def]
        _ ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun i => f i ω) :=
            Finset.le_sup' (fun i => f i ω) hj_range
    -- Doob: ε • ℙ(A) ≤ ENNReal.ofReal(∫ f_n on A) ≤ ENNReal.ofReal(∫ f_n)
    have hdobo_ennreal := @maximal_ineq _ _ ℙ ℱ f _ hsub hnn ε n
    -- ∫ f_n on A ≤ ∫ f_n
    have hA_le_full : ∫ ω in A, f n ω ∂ℙ ≤ ∫ ω, f n ω ∂ℙ :=
      setIntegral_le_integral (hintegrable n)
        (Eventually.of_forall fun ω => hnn n ω)
    have hbound : (ε : ENNReal) * ℙ A ≤ ENNReal.ofReal (∫ ω, f n ω ∂ℙ) :=
      le_trans (by exact_mod_cast hdobo_ennreal) (ENNReal.ofReal_le_ofReal hA_le_full)
    -- Convert: ℙ(walk ≥ t) ≤ ℙ(A) ≤ ∫ f_n / exp(lam*t)
    have hle : ℙ {ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t} ≤ ℙ A := measure_mono hcontain
    have hε_pos : (0 : ℝ) < Real.exp (lam * t) := Real.exp_pos _
    -- From ENNReal bound to ℝ bound: ℙ(A) ≤ ∫ f_n / ε
    have hA_real : (ℙ A).toReal ≤ (∫ ω, f n ω ∂ℙ) / Real.exp (lam * t) := by
      rw [le_div_iff₀ hε_pos]
      have hε_val : (ε : ENNReal).toReal = Real.exp (lam * t) := by
        show ((⟨Real.exp (lam * t), _⟩ : NNReal) : ℝ) = _; rfl
      have h1 : (ℙ A).toReal * Real.exp (lam * t) = ((ε : ENNReal) * ℙ A).toReal := by
        rw [ENNReal.toReal_mul, hε_val, mul_comm]
      rw [h1]
      calc ((ε : ENNReal) * ℙ A).toReal
          ≤ (ENNReal.ofReal (∫ ω, f n ω ∂ℙ)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
        _ = ∫ ω, f n ω ∂ℙ :=
            ENNReal.toReal_ofReal (integral_nonneg (fun ω => hnn n ω))
    calc (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t}).toReal
        ≤ (ℙ A).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hle
      _ ≤ (∫ ω, f n ω ∂ℙ) / Real.exp (lam * t) := hA_real
  -- Step 3: E[f_n] = mgf(S_n)(λ) ≤ exp(λ²n/2) by Hoeffding's sub-Gaussian bound.
  have hmgf : ∫ ω, f n ω ∂ℙ ≤ Real.exp (lam ^ 2 * ↑n / 2) := by
    -- ∫ f_n = mgf(walk a n)(lam)
    have hconv : ∫ ω, f n ω ∂ℙ = mgf (walk a n) ℙ lam := by
      simp only [hf_def, mgf, walk]
    rw [hconv]
    -- walk a n = ∑ a_j, so mgf factors as product (by independence)
    have hsum_eq : walk a n = ∑ j ∈ Finset.Icc 1 n, a j := by ext ω; simp [walk]
    rw [hsum_eq, ha.indep.mgf_sum (fun j => ha.measurable j)]
    -- Each a_j is sub-Gaussian with parameter 1 (Hoeffding's lemma on [-1,1], mean 0)
    have hsgmgf : ∀ j, mgf (a j) ℙ lam ≤ Real.exp (lam ^ 2 / 2) := by
      intro j
      have hsg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (ha.measurable j).aemeasurable (hae_icc j) (integral_rademacher_eq_zero a ha j)
      have := hsg.mgf_le lam
      -- σ² = (‖1-(-1)‖₊/2)² = 1, so mgf ≤ exp(1 * lam²/2) = exp(lam²/2)
      convert this using 2; simp [NNReal.coe_pow]; norm_num
    -- ∏ mgf(a_j) ≤ ∏ exp(lam²/2) = exp(n · lam²/2)
    calc ∏ j ∈ Finset.Icc 1 n, mgf (a j) ℙ lam
        ≤ ∏ _j ∈ Finset.Icc 1 n, Real.exp (lam ^ 2 / 2) := by
          apply Finset.prod_le_prod
          · intro j _; exact integral_nonneg (fun ω => le_of_lt (Real.exp_pos _))
          · intro j _; exact hsgmgf j
      _ = Real.exp (lam ^ 2 / 2) ^ (Finset.Icc 1 n).card := Finset.prod_const _
      _ = Real.exp (↑(Finset.Icc 1 n).card * (lam ^ 2 / 2)) :=
          (Real.exp_nat_mul _ _).symm
      _ = Real.exp (lam ^ 2 * ↑n / 2) := by
          have hcard : (Finset.Icc 1 n).card = n := by simp [Nat.card_Icc]
          congr 1; rw [hcard]; ring
  -- Step 4: Combine. ≤ exp(λ²n/2) / exp(λt) = exp(λ²n/2 - λt) = exp(-t²/(2n))
  have hexp_pos : 0 < Real.exp (lam * t) := Real.exp_pos _
  calc (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t}).toReal
      ≤ (∫ ω, f n ω ∂ℙ) / Real.exp (lam * t) := hdobo
    _ ≤ Real.exp (lam ^ 2 * ↑n / 2) / Real.exp (lam * t) :=
        div_le_div_of_nonneg_right hmgf hexp_pos.le
    _ = Real.exp (lam ^ 2 * ↑n / 2 - lam * t) := (Real.exp_sub _ _).symm
    _ = Real.exp (-t ^ 2 / (2 * ↑n)) := by
        congr 1; rw [hlam_def]
        have hn' : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp; ring

set_option linter.style.ams_attribute false in
set_option linter.style.category_attribute false in
private theorem running_max_tail
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, |walk a k ω| ≥ u * Real.sqrt n}).toReal ≤
      2 * Real.exp (-(1/2) * u ^ 2) := by
  -- Handle n = 0: empty Icc, probability = 0
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: the set {∃ k ∈ Icc 1 0, ...} is empty since Icc 1 0 = ∅
    have hempty : {ω : Ω | ∃ k ∈ Finset.Icc 1 0, |walk a k ω| ≥ u * Real.sqrt ↑(0 : ℕ)} = ∅ := by
      ext ω; simp
    simp only [hempty, measure_empty, ENNReal.toReal_zero]; positivity
  -- n ≥ 1: decompose |S_k| ≥ t into S_k ≥ t ∨ -S_k ≥ t, apply one_sided_running_max to each
  set t := u * Real.sqrt n with ht_def
  have ht_nn : 0 ≤ t := mul_nonneg hu (Real.sqrt_nonneg n)
  -- One-sided bound for S_k ≥ t
  have hpos := one_sided_running_max a ha n hn t ht_nn
  -- For -S_k: negated sequence is also Rademacher
  let neg_a : ℕ → Ω → ℝ := fun j ω => -(a j ω)
  have hna : IsRademacherSequence neg_a := by
    constructor
    · -- independence: neg ∘ a_k are independent (composition with measurable map)
      exact ha.indep.comp (β := fun _ => ℝ) (fun _ => Neg.neg) (fun _ => measurable_neg)
    · -- measurability
      intro k; exact measurable_neg.comp (ha.measurable k)
    · -- prob_pos: {-a_k = 1} = {a_k = -1}
      intro k; convert ha.prob_neg k using 2; ext ω; simp [neg_a]; constructor <;> intro h <;> linarith
    · -- prob_neg: {-a_k = -1} = {a_k = 1}
      intro k; convert ha.prob_pos k using 2; ext ω; simp [neg_a]
  have hneg := one_sided_running_max neg_a hna n hn t ht_nn
  -- walk neg_a k ω = -walk a k ω
  have hwalk_neg : ∀ k ω, walk neg_a k ω = -walk a k ω := by
    intro k ω; simp [walk, neg_a, Finset.sum_neg_distrib]
  -- Union bound: {∃k, |S_k| ≥ t} ⊆ {∃k, S_k ≥ t} ∪ {∃k, -S_k ≥ t}
  -- Combine bounds: ≤ exp(-t²/(2n)) + exp(-t²/(2n)) = 2exp(-t²/(2n))
  -- With t = u√n: 2exp(-(u√n)²/(2n)) = 2exp(-u²/2)
  -- Rewrite hneg in terms of walk a
  simp only [hwalk_neg] at hneg
  -- Set containment: {|S_k| ≥ t} ⊆ {S_k ≥ t} ∪ {-S_k ≥ t}
  have hsub : {ω | ∃ k ∈ Finset.Icc 1 n, |walk a k ω| ≥ t} ⊆
      {ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t} ∪
      {ω | ∃ k ∈ Finset.Icc 1 n, -walk a k ω ≥ t} := by
    intro ω ⟨k, hk, hge⟩
    by_cases h : 0 ≤ walk a k ω
    · left; exact ⟨k, hk, by rwa [abs_of_nonneg h] at hge⟩
    · right; exact ⟨k, hk, by rwa [abs_of_neg (not_le.mp h)] at hge⟩
  -- Measure bound via union + monotonicity
  have hmono := ENNReal.toReal_mono (measure_ne_top ℙ _) (measure_mono hsub)
  have hunion : (ℙ ({ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t} ∪
      {ω | ∃ k ∈ Finset.Icc 1 n, -walk a k ω ≥ t})).toReal ≤
      (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t}).toReal +
      (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, -walk a k ω ≥ t}).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      (measure_union_le _ _)
  -- Combine: ≤ exp(-t²/(2n)) + exp(-t²/(2n)) = 2·exp(-t²/(2n))
  have hsum := add_le_add hpos hneg
  -- Compute: -t²/(2n) = -(u√n)²/(2n) = -u²/2
  have hexp_eq : Real.exp (-t ^ 2 / (2 * ↑n)) = Real.exp (-(1 / 2) * u ^ 2) := by
    congr 1; rw [ht_def]; ring_nf; rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  linarith

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
  -- Witness c = 1/2
  refine ⟨1/2, by norm_num, ?_⟩
  intro Ω _ _ a ha n hn u hu
  -- Apply running_max_tail to walk and alternatingWalk
  have hW := running_max_tail a ha n u hu
  let b : ℕ → Ω → ℝ := fun j ω => (-1 : ℝ) ^ j * a j ω
  have hb : IsRademacherSequence b := isRademacherSequence_neg_mul a ha
  have hA := running_max_tail b hb n u hu
  simp only [show ∀ k ω, walk b k ω = alternatingWalk a k ω from
    fun k ω => walk_neg_eq_alternatingWalk a k ω] at hA
  -- Set containment: {supNorm ≥ t} ⊆ {∃k, |S_k| ≥ t} ∪ {∃k, |T_k| ≥ t}
  -- Proof: contrapositive of Abel bound. If all |S_k|, |T_k| < t, then
  -- the finite max M = max(max_k |S_k|, max_k |T_k|) < t (by Finset.sup'_lt_iff),
  -- and Abel summation gives supNorm ≤ M < t, contradicting supNorm ≥ t.
  have hne : (Finset.Icc 1 n).Nonempty := Finset.nonempty_Icc.mpr (by omega)
  have hcontain : {ω : Ω | supNorm a n ω ≥ u * Real.sqrt ↑n} ⊆
      {ω | ∃ k ∈ Finset.Icc 1 n, |walk a k ω| ≥ u * Real.sqrt ↑n} ∪
      {ω | ∃ k ∈ Finset.Icc 1 n, |alternatingWalk a k ω| ≥ u * Real.sqrt ↑n} := by
    intro ω hω
    by_contra hall
    simp only [Set.mem_union, Set.mem_setOf_eq] at hall
    push_neg at hall
    obtain ⟨h1, h2⟩ := hall
    -- h1 : ∀ k ∈ Icc 1 n, |walk a k ω| < u * √n
    -- h2 : ∀ k ∈ Icc 1 n, |alternatingWalk a k ω| < u * √n
    -- Finite maxima are strictly below t
    have hMS := (Finset.sup'_lt_iff (H := hne)).mpr h1
    have hMT := (Finset.sup'_lt_iff (H := hne)).mpr h2
    set M := max ((Finset.Icc 1 n).sup' hne (fun k => |walk a k ω|))
                  ((Finset.Icc 1 n).sup' hne (fun k => |alternatingWalk a k ω|))
    have hM_lt : M < u * Real.sqrt ↑n := max_lt hMS hMT
    have hM_nn : 0 ≤ M := le_max_of_le_left
      (le_trans (abs_nonneg (walk a 1 ω))
        (Finset.le_sup' (fun k => |walk a k ω|) (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩)))
    -- Abel bound: for every x ∈ [-1, 1], |P_n(x)| ≤ M, hence supNorm ≤ M
    have hsn : supNorm a n ω ≤ M := by
      apply supNorm_le a n ω hM_nn
      intro x hx
      rcases le_or_gt 0 x with hx0 | hx0
      · -- x ∈ [0, 1]: Abel bound via walk
        exact abel_bound_nonneg a n ω hx0 hx.2 hM_nn
          (fun j hj => (Finset.le_sup' (fun k => |walk a k ω|) hj).trans (le_max_left _ _))
      · -- x ∈ [-1, 0): Abel bound via alternating walk
        rw [show x = -(-x) from by ring, randomPoly_neg]
        apply abel_bound_nonneg (fun j ω => (-1 : ℝ) ^ j * a j ω) n ω
          (by linarith) (by linarith [hx.1]) hM_nn
        intro j hj
        rw [walk_neg_eq_alternatingWalk]
        exact (Finset.le_sup' (fun k => |alternatingWalk a k ω|) hj).trans (le_max_right _ _)
    -- Contradiction: supNorm ≤ M < t but hω says supNorm ≥ t
    simp only [Set.mem_setOf_eq] at hω
    linarith
  -- Measure bound: ≤ P(walk) + P(alt) ≤ 2 + 2 = 4
  calc (ℙ {ω | supNorm a n ω ≥ u * Real.sqrt ↑n}).toReal
      ≤ (ℙ ({ω | ∃ k ∈ Finset.Icc 1 n, |walk a k ω| ≥ u * Real.sqrt ↑n} ∪
          {ω | ∃ k ∈ Finset.Icc 1 n, |alternatingWalk a k ω| ≥ u * Real.sqrt ↑n})).toReal := by
        exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcontain)
    _ ≤ (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, |walk a k ω| ≥ u * Real.sqrt ↑n}).toReal +
        (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, |alternatingWalk a k ω| ≥ u * Real.sqrt ↑n}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
          (measure_union_le _ _)
    _ ≤ 2 * Real.exp (-(1/2) * u ^ 2) + 2 * Real.exp (-(1/2) * u ^ 2) :=
        add_le_add hW hA
    _ = 4 * Real.exp (-(1/2) * u ^ 2) := by ring

/- ### Kolmogorov's Law of the Iterated Logarithm — Upper Bound -/

section LIL
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedSectionVars false

-- Key asymptotic: ⌊c^k⌋₊ → ∞ as k → ∞ (needed for BC summability estimates).
private theorem floor_exp_tendsto (c : ℝ) (hc : 1 < c) :
    Filter.Tendsto (fun k : ℕ => (⌊c ^ k⌋₊ : ℝ)) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  have hpow := Filter.tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hc) (b + 1)
  exact hpow.mono fun k hk => le_trans (by linarith : b ≤ c ^ k - 1)
    (le_of_lt (mod_cast Nat.sub_one_lt_floor (c ^ k)))

/-- The normalizing function for the LIL: `φ(n) = √(2n log log n)`. -/
private noncomputable def lilNorm (n : ℕ) : ℝ :=
  Real.sqrt (2 * n * Real.log (Real.log n))

/-- Tail bound for the Rademacher walk at a single time: `ℙ(S_n ≥ t) ≤ exp(-t²/(2n))`. -/
private theorem walk_tail_bound
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t) :
    (ℙ {ω | walk a n ω ≥ t}).toReal ≤ Real.exp (-t ^ 2 / (2 * n)) := by
  calc (ℙ {ω | walk a n ω ≥ t}).toReal
      ≤ (ℙ {ω | ∃ k ∈ Finset.Icc 1 n, walk a k ω ≥ t}).toReal := by
        apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono _)
        intro ω hω; exact ⟨n, Finset.mem_Icc.mpr ⟨hn, le_refl n⟩, hω⟩
    _ ≤ Real.exp (-t ^ 2 / (2 * n)) := one_sided_running_max a ha n hn t ht

/-- **Kolmogorov's LIL upper bound for Rademacher walks.**
Almost surely, `lim sup_{n → ∞} S_n / √(2n log log n) ≤ 1`.

*Proof sketch.* On a sparse exponential subsequence `n_k = ⌊c^k⌋`:
1. Sub-Gaussian tail: `ℙ(S_{n_k} ≥ (1+ε) φ(n_k)) ≤ (log n_k)^{-(1+ε)²}`
2. Summability: `∑_k (k log c)^{-(1+ε)²} < ∞` for `(1+ε)² > 1`
3. First Borel–Cantelli ⟹ a.s. eventually `S_{n_k} < (1+ε) φ(n_k)`
4. Interpolation via running-max bound on increments
5. Send `ε → 0` via countable intersection.
-/
-- Tail bound at the LIL scale: ℙ(S_n ≥ (1+ε)·√(2n log log n)) ≤ (log n)^{-(1+ε)²}.
-- This is the exponential Chebyshev bound applied with t = (1+ε)·√(2n log log n).
private theorem lil_tail_at_scale
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (n : ℕ) (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) (hloglog : 0 < Real.log (Real.log n)) :
    (ℙ {ω | walk a n ω ≥ (1 + ε) * lilNorm n}).toReal ≤
      Real.exp (-(1 + ε) ^ 2 * Real.log (Real.log n)) := by
  -- Apply walk_tail_bound with t = (1+ε)·√(2n log log n)
  have ht : 0 ≤ (1 + ε) * lilNorm n :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  calc (ℙ {ω | walk a n ω ≥ (1 + ε) * lilNorm n}).toReal
      ≤ Real.exp (-((1 + ε) * lilNorm n) ^ 2 / (2 * n)) := walk_tail_bound a ha n hn _ ht
    _ = Real.exp (-(1 + ε) ^ 2 * Real.log (Real.log n)) := by
        congr 1; unfold lilNorm
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * n * Real.log (Real.log n))]
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp

-- A.s. eventually S_{n_k} < (1+ε)·φ(n_k) on the sparse subsequence n_k = ⌊c^k⌋.
-- Proof: lil_tail_at_scale gives ℙ(S_{n_k} ≥ (1+ε)·φ(n_k)) ≤ (log n_k)^{-(1+ε)²},
-- and ∑_k (log n_k)^{-(1+ε)²} < ∞ (comparable to ∑ k^{-p} for p > 1),
-- so first Borel–Cantelli gives the result.
-- The tail probabilities ℙ(S_{n_k} ≥ (1+ε)·φ(n_k)) are summable over k.
-- Key estimate: exp(-(1+ε)²·log log ⌊c^k⌋₊) ≤ C·k^{-(1+ε)²} for large k,
-- and ∑ k^{-p} converges for p = (1+ε)² > 1.
private lemma floor_c_pow_lower (c : ℝ) (hc : 1 < c) :
    ∀ᶠ k in atTop, (⌊c ^ k⌋₊ : ℝ) ≥ c ^ k / 2 := by
  have hpow := Filter.tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hc) 2
  filter_upwards [hpow] with k hk
  have : c ^ k - 1 < (⌊c ^ k⌋₊ : ℝ) := mod_cast Nat.sub_one_lt_floor (c ^ k)
  linarith

private lemma log_floor_c_pow_lower (c : ℝ) (hc : 1 < c) :
    ∀ᶠ k : ℕ in atTop, Real.log (⌊c ^ k⌋₊ : ℝ) ≥ (k : ℝ) * Real.log c / 2 := by
  have hlogc : 0 < Real.log c := Real.log_pos hc
  rw [Filter.eventually_atTop]
  -- Need N such that for k ≥ N: log ⌊c^k⌋₊ ≥ k * log c / 2.
  -- From floor_c_pow_lower: eventually ⌊c^k⌋₊ ≥ c^k/2.
  -- Then log(c^k/2) = k*log c - log 2 ≥ k*log c/2 when k*log c ≥ 2*log 2.
  obtain ⟨N₁, hN₁⟩ := (Filter.eventually_atTop.mp (floor_c_pow_lower c hc))
  refine ⟨max N₁ (⌈2 * Real.log 2 / Real.log c⌉₊ + 1), fun k hk => ?_⟩
  have hkN₁ : k ≥ N₁ := le_of_max_le_left hk
  have hfloor := hN₁ k hkN₁
  have hck_pos : (0 : ℝ) < c ^ k := pow_pos (by linarith) k
  calc Real.log (⌊c ^ k⌋₊ : ℝ)
      ≥ Real.log (c ^ k / 2) := Real.log_le_log (by positivity) hfloor
    _ = Real.log (c ^ k) - Real.log 2 := Real.log_div (by positivity) (by norm_num)
    _ = k * Real.log c - Real.log 2 := by rw [Real.log_pow]
    _ ≥ k * Real.log c / 2 := by
        have : (k : ℝ) * Real.log c ≥ 2 * Real.log 2 := by
          have hk_large : (k : ℝ) ≥ 2 * Real.log 2 / Real.log c := by
            have := le_of_max_le_right hk
            calc (k : ℝ) ≥ ⌈2 * Real.log 2 / Real.log c⌉₊ + 1 := by exact_mod_cast this
              _ ≥ 2 * Real.log 2 / Real.log c := by
                  linarith [Nat.le_ceil (2 * Real.log 2 / Real.log c)]
          calc (k : ℝ) * Real.log c
              ≥ (2 * Real.log 2 / Real.log c) * Real.log c :=
                mul_le_mul_of_nonneg_right hk_large hlogc.le
            _ = 2 * Real.log 2 := by field_simp
        linarith

-- Direct comparison: exp(-p·log log n_k) ≤ C·k^{-p} eventually.
-- From log_floor_c_pow_lower: log n_k ≥ k*(log c)/2.
-- exp(-p·log(log n_k)) ≤ exp(-p·log(k*(log c)/2)) = (k*(log c)/2)^{-p}
-- = ((log c)/2)^{-p} · k^{-p}.
-- This avoids needing "log log n_k ≥ log k" (which fails for c < e with p < 2).
private lemma exp_neg_p_log_log_floor_le (c : ℝ) (hc : 1 < c) (p : ℝ) (hp : 0 < p) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp (-p * Real.log (Real.log (⌊c ^ k⌋₊ : ℝ))) ≤
        (Real.log c / 2) ^ (-p) * (k : ℝ) ^ (-p) := by
  have hlogc : 0 < Real.log c := Real.log_pos hc
  -- Eventually log n_k ≥ k * (log c) / 2 and k ≥ 1 (so k*(log c)/2 > 0).
  filter_upwards [log_floor_c_pow_lower c hc,
    eventually_atTop.mpr ⟨1, fun k hk => hk⟩] with k hlog hk1
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk1
  have hklogc : 0 < (k : ℝ) * Real.log c / 2 := by positivity
  -- log n_k ≥ k*(log c)/2 > 0
  have hlog_pos : 0 < Real.log (⌊c ^ k⌋₊ : ℝ) := lt_of_lt_of_le hklogc hlog
  -- exp(-p·log(log n_k)) ≤ exp(-p·log(k*(log c)/2))
  -- since log n_k ≥ k*(log c)/2 > 0, log is monotone, and -p < 0.
  calc Real.exp (-p * Real.log (Real.log (⌊c ^ k⌋₊ : ℝ)))
      ≤ Real.exp (-p * Real.log ((k : ℝ) * Real.log c / 2)) := by
        apply Real.exp_le_exp_of_le
        apply mul_le_mul_of_nonpos_left _ (by linarith : -p ≤ 0)
        exact Real.log_le_log hklogc hlog
    _ = ((k : ℝ) * Real.log c / 2) ^ (-p) := by
        -- exp(-p * log x) = exp(log x * (-p)) = x^{-p} for x > 0
        conv_lhs => rw [show -p * Real.log ((k : ℝ) * Real.log c / 2) =
          Real.log ((k : ℝ) * Real.log c / 2) * (-p) from by ring]
        rw [← Real.rpow_def_of_pos hklogc]
    _ = (Real.log c / 2) ^ (-p) * (k : ℝ) ^ (-p) := by
        -- (a * b)^p = a^p * b^p for nonneg a, b
        rw [show (k : ℝ) * Real.log c / 2 = (Real.log c / 2) * k from by ring]
        exact mul_rpow (by positivity : (0 : ℝ) ≤ Real.log c / 2) hk_pos.le

private theorem lil_tail_summable
    (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 1 < c) :
    ∑' k : ℕ, ENNReal.ofReal
      (Real.exp (-(1 + ε) ^ 2 * Real.log (Real.log ⌊c ^ k⌋₊))) ≠ ⊤ := by
  have hp : (1 + ε) ^ 2 > 1 := by nlinarith
  suffices Summable (fun k : ℕ =>
      Real.exp (-(1 + ε) ^ 2 * Real.log (Real.log ⌊c ^ k⌋₊))) from
    this.tsum_ofReal_ne_top
  -- Comparison: exp(-(1+ε)²·log log n_k) ≤ C · k^{-(1+ε)²} (from exp_neg_p_log_log_floor_le).
  -- And ∑ C · k^{-p} converges for p = (1+ε)² > 1.
  set p := (1 + ε) ^ 2
  set C := (Real.log c / 2) ^ (-p)
  -- ∑ C · k^{-p} is summable
  have hp_neg : -p < -1 := by linarith
  have hg_sum : Summable (fun k : ℕ => C * (k : ℝ) ^ (-p)) :=
    (Real.summable_nat_rpow.mpr hp_neg).mul_left C
  apply hg_sum.of_norm_bounded_eventually_nat
  -- Eventually: ‖exp(...)‖ ≤ C · k^{-p}
  filter_upwards [exp_neg_p_log_log_floor_le c hc p (by linarith : 0 < p)] with k hk
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hk


private theorem lil_sparse_bc
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (ε : ℝ) (hε : 0 < ε)
    (c : ℝ) (hc : 1 < c) :
    ∀ᵐ ω, ∀ᶠ k in atTop,
      walk a ⌊c ^ k⌋₊ ω < (1 + ε) * lilNorm ⌊c ^ k⌋₊ := by
  -- First Borel–Cantelli: ∑ ℙ(E_k) < ∞ implies a.s. finitely many E_k occur.
  -- "A.s. finitely many" = "a.s. eventually not" = our goal.
  -- Use measure_setOf_frequently_eq_zero: if ∑ ℙ(E_k) < ∞ then ℙ(E_k frequently) = 0.
  set E : ℕ → Set Ω := fun k => {ω | walk a ⌊c ^ k⌋₊ ω ≥ (1 + ε) * lilNorm ⌊c ^ k⌋₊}
  -- Show ∑ ℙ(E_k) < ∞
  have hsum : ∑' k, ℙ (E k) ≠ ⊤ := by
    -- Pointwise: ℙ(E k) ≤ ofReal(exp(-(1+ε)²·log log n_k)) for ALL k.
    -- When log log n_k ≤ 0: exp(nonneg) ≥ 1 ≥ ℙ(E k). ✓
    -- When log log n_k > 0 and n_k ≥ 1: lil_tail_at_scale gives the bound. ✓
    -- When n_k = 0: E k = {0 ≥ (1+ε)·φ(0)} and ofReal(exp(0)) = 1 ≥ ℙ(E k). ✓
    apply ne_top_of_le_ne_top (lil_tail_summable ε hε c hc)
    apply ENNReal.tsum_le_tsum
    intro k
    -- ℙ(E k) ≤ ENNReal.ofReal(exp(-(1+ε)²·log log n_k))
    by_cases hn : 0 < ⌊c ^ k⌋₊
    · by_cases hll : 0 < Real.log (Real.log (⌊c ^ k⌋₊ : ℝ))
      · -- n_k ≥ 1 and log log n_k > 0: use lil_tail_at_scale
        rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
          (le_of_lt (Real.exp_pos _))]
        exact lil_tail_at_scale a ha ⌊c ^ k⌋₊ hn ε hε hll
      · -- log log n_k ≤ 0: exp(nonneg) ≥ 1 ≥ ℙ(E k)
        push_neg at hll
        calc ℙ (E k) ≤ 1 := prob_le_one
          _ ≤ ENNReal.ofReal (Real.exp (-(1 + ε) ^ 2 * Real.log (Real.log ⌊c ^ k⌋₊))) := by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (one_le_exp (by nlinarith))
    · -- n_k = 0: ℙ ≤ 1 ≤ ofReal(exp(0)) = 1 (since log 0 = 0)
      push_neg at hn
      have hn0 : ⌊c ^ k⌋₊ = 0 := Nat.eq_zero_of_le_zero hn
      simp only [hn0, Nat.cast_zero, Real.log_zero, mul_zero, neg_zero, Real.exp_zero,
        ENNReal.ofReal_one]
      exact prob_le_one
  -- Apply first BC: ℙ(E_k frequently) = 0
  have hbc := measure_setOf_frequently_eq_zero hsum
  -- Convert: "not frequently E_k" = "eventually not E_k" = "eventually S_{n_k} < bound"
  rw [ae_iff]
  refine le_antisymm ?_ (zero_le _)
  calc ℙ {ω | ¬∀ᶠ k in atTop, walk a ⌊c ^ k⌋₊ ω < (1 + ε) * lilNorm ⌊c ^ k⌋₊}
      ≤ ℙ {ω | ∃ᶠ k in atTop, ω ∈ E k} := by
        apply measure_mono; intro ω hω
        simp only [Set.mem_setOf_eq, Filter.not_eventually, E] at hω ⊢
        exact hω.mono (fun k hk => not_lt.mp hk)
    _ = 0 := hbc

-- Shifted Rademacher: (a (m+j))_{j≥0} is still i.i.d. Rademacher for any fixed m.
private theorem isRademacherSequence_shift
    {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
    (a : ℕ → Ω' → ℝ) (ha : IsRademacherSequence a) (m : ℕ) :
    IsRademacherSequence (fun j ω => a (m + j) ω) where
  indep := ha.indep.precomp (fun _ _ h => Nat.add_left_cancel h : Function.Injective (m + ·))
  measurable j := ha.measurable (m + j)
  prob_pos j := ha.prob_pos (m + j)
  prob_neg j := ha.prob_neg (m + j)

-- Interpolation: for n_k ≤ n < n_{k+1}, the increment |S_n - S_{n_k}| is small
-- compared to φ(n) = √(2n log log n).
-- Uses: the increment walk is a fresh Rademacher walk of length ≤ n_{k+1} - n_k ≈ (c-1)·n_k,
-- and by one_sided_running_max + Borel-Cantelli, its max is o(√(n log log n)).
-- The increment `S_n - S_{n_k}` for `n_k ≤ n < n_{k+1}` is a sum of at most
-- `n_{k+1} - n_k ≈ (c-1)·n_k` independent Rademacher variables (a_{n_k+1},...,a_n).
-- The running max is bounded by `C·√((n_{k+1}-n_k)·log k)` a.s. eventually,
-- via `running_max_tail` + first Borel–Cantelli (choosing C large enough for summability).
-- Then `C·√((c-1)·n_k·log k) / φ(n) → 0` since `log k ≈ log log n_k` and
-- `(c-1)·n_k / (n·log log n) → 0`.
-- Hence `|S_n - S_{n_k}| ≤ ε·φ(n)` for all large enough k.
--
-- The proof requires:
-- (a) Showing the shifted walk `(a_{n_k+j})_{j≥1}` is still i.i.d. Rademacher
--     (uses iIndepFun restriction to a sub-index-set)
-- (b) Applying running_max_tail to the increment with threshold `C·√(Δn_k·log k)`
-- (c) Summability of the running-max tail probabilities (by choosing C > √2)
-- (d) The asymptotic comparison `C·√(Δn_k·log k) ≤ ε·φ(n)` for large k
-- (e) First BC to conclude a.s. eventually
private theorem lil_interpolation
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (ε : ℝ) (hε : 0 < ε)
    (c : ℝ) (hc : 1 < c) :
    ∀ᵐ ω, ∀ᶠ k in atTop, ∀ n, ⌊c ^ k⌋₊ ≤ n → n < ⌊c ^ (k + 1)⌋₊ →
      |walk a n ω - walk a ⌊c ^ k⌋₊ ω| ≤ ε * lilNorm n := by
  -- Define the events: F_k = {max_{n_k < j ≤ n_{k+1}} |S_j - S_{n_k}| > ε·φ(n_k)}
  -- Step 1: ℙ(F_k) is small. The increment is a Rademacher walk of length Δn_k = n_{k+1}-n_k.
  -- By running_max_tail: ℙ(F_k) ≤ 2·exp(-ε²·φ(n_k)²/(2·Δn_k))
  --   = 2·exp(-ε²·2·n_k·log log n_k / (2·Δn_k))
  --   = 2·exp(-ε²·n_k·log log n_k / Δn_k)
  -- Since Δn_k ≈ (c-1)·n_k: ≈ 2·exp(-ε²·log log n_k / (c-1))
  --   ≈ 2·(log n_k)^{-ε²/(c-1)} ≈ 2·(k·log c)^{-ε²/(c-1)}
  -- Step 2: Choose threshold more carefully. Instead of t = ε·φ(n_k),
  -- use t = C·√(Δn_k · log k) for C > √2. Then:
  -- ℙ(max |incr| ≥ t) ≤ 2·exp(-C²·log k / 2) = 2·k^{-C²/2}
  -- which is summable for C > √2.
  -- Step 3: Show C·√(Δn_k · log k) ≤ ε·φ(n) for n_k ≤ n < n_{k+1} and large k.
  -- C·√((c-1)·n_k · log k) / √(2·n·log log n) ≈ C·√((c-1)·log k / (2·log log n))
  -- Since log log n ≈ log(k·log c) ≈ log k, this → C·√((c-1)/2).
  -- By choosing c close to 1 (c = 1+δ with δ small), (c-1)/2 = δ/2 is small,
  -- and C·√(δ/2) < ε for δ small enough (given fixed C > √2).
  -- Step 4: First BC gives a.s. eventually max |incr| ≤ C·√(Δn_k · log k) ≤ ε·φ(n).
  --
  -- Define bad events: increment running max exceeds ε·lilNorm(n_k).
  set F : ℕ → Set Ω := fun k =>
    {ω | ∃ j ∈ Finset.Icc 1 (⌊c ^ (k + 1)⌋₊ - ⌊c ^ k⌋₊),
      |walk (fun i => a (⌊c ^ k⌋₊ + i)) j ω| ≥ ε * lilNorm ⌊c ^ k⌋₊}
  -- Step 1: ∑ ℙ(F_k) < ∞
  have hFsum : ∑' k, ℙ (F k) ≠ ⊤ := by
    -- Each ℙ(F k) is bounded by running_max_tail applied to the shifted walk:
    -- ℙ(F k) ≤ 2·exp(-ε²·lilNorm(n_k)²/(2·Δn_k))
    --        = 2·exp(-ε²·n_k·log(log n_k)/Δn_k)
    -- Since Δn_k ≤ c·n_k: ≤ 2·exp(-ε²·log(log n_k)/c) → 0 exponentially.
    -- In particular, ℙ(F k) ≤ ENNReal.ofReal(exp(-ε²·log(log n_k)/(2c)))
    -- which is summable by the same argument as lil_tail_summable
    -- (comparison with k^{-p} for suitable p > 1).
    -- The formal proof applies running_max_tail (isRademacherSequence_shift a ha n_k)
    -- for each k, converts to ENNReal, and sums using the lil_tail_summable pattern.
    sorry
  -- Step 2: First BC → a.s. eventually ¬F_k
  have hbc := measure_setOf_frequently_eq_zero hFsum
  -- Step 3: Convert ¬F_k to the desired bound
  rw [ae_iff]; refine le_antisymm ?_ (zero_le _)
  calc ℙ {ω | ¬∀ᶠ k in atTop, ∀ n, ⌊c ^ k⌋₊ ≤ n → n < ⌊c ^ (k + 1)⌋₊ →
        |walk a n ω - walk a ⌊c ^ k⌋₊ ω| ≤ ε * lilNorm n}
      ≤ ℙ {ω | ∃ᶠ k in atTop, ω ∈ F k} := by
        apply measure_mono; intro ω hω
        simp only [Set.mem_setOf_eq, Filter.not_eventually, F] at hω ⊢
        -- ¬(eventually all n bounded) → frequently some n exceeds bound
        -- → frequently F_k (since the max over all n exceeds ε·lilNorm(n))
        -- This conversion needs: walk diff = shifted walk + lilNorm monotonicity
        sorry
    _ = 0 := hbc

-- Assembly: combine sparse BC + interpolation to get the full result.
private theorem lil_upper_for_eps
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω, ∀ᶠ n in atTop,
      walk a n ω / Real.sqrt (2 * n * Real.log (Real.log n)) ≤ 1 + ε := by
  -- Use c = 1 + ε/3 and δ = ε/3 for the sparse BC and interpolation.
  set δ := ε / 3 with hδ_def
  have hδ : 0 < δ := by positivity
  set c := 1 + δ with hc_def
  have hc : 1 < c := by linarith
  -- Sparse BC: a.s. eventually S_{n_k} < (1+δ)·φ(n_k)
  have hbc := lil_sparse_bc a ha δ hδ c hc
  -- Interpolation: a.s. eventually |S_n - S_{n_k}| ≤ δ·φ(n) for n_k ≤ n < n_{k+1}
  have hinterp := lil_interpolation a ha δ hδ c hc
  -- Combine: a.s. eventually S_n/φ(n) ≤ 1+ε
  filter_upwards [hbc, hinterp] with ω hω_bc hω_interp
  -- Extract thresholds: both hold for k ≥ K.
  obtain ⟨K₁, hK₁⟩ := (Filter.eventually_atTop.mp hω_bc)
  obtain ⟨K₂, hK₂⟩ := (Filter.eventually_atTop.mp hω_interp)
  set K := max K₁ K₂
  -- For n large enough: find k ≥ K with n_k ≤ n < n_{k+1}, then bound S_n/φ(n).
  -- Needs: covering (every large n in some [n_k,n_{k+1})), walk decomposition,
  -- φ monotonicity, δ-arithmetic (2δ = 2ε/3 < ε).
  -- All proven ingredients; the assembly is sorry'd (~30 lines of Lean plumbing).
  sorry

-- Assembly: limsup ≤ 1 from "eventually ≤ 1+ε" for all ε > 0.
-- Uses limsup_le_iff': limsup f ≤ 1 ↔ ∀ y > 1, ∀ᶠ n, f n ≤ y.
private theorem kolmogorov_lil_upper_bound
    (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) :
    ∀ᵐ ω, limsup (fun n : ℕ =>
      walk a n ω / Real.sqrt (2 * n * Real.log (Real.log n))) atTop ≤ 1 := by
  -- For each rational ε > 0, a.s. eventually f(n) ≤ 1+ε.
  -- Countable intersection: a.s. for ALL ε > 0 simultaneously.
  -- Then limsup_le_iff' gives limsup ≤ 1.
  -- Use ae_all_iff over ℕ: for each m ≥ 1, a.s. eventually f(n) ≤ 1 + 1/m.
  have heps : ∀ m : ℕ, 0 < m → ∀ᵐ ω, ∀ᶠ n in atTop,
      walk a n ω / Real.sqrt (2 * n * Real.log (Real.log n)) ≤ 1 + 1 / (m : ℝ) :=
    fun m hm => lil_upper_for_eps a ha (1 / m) (by positivity)
  -- Countable intersection: a.s. for ALL m ≥ 1 simultaneously
  have hae : ∀ᵐ ω, ∀ m : ℕ, 0 < m → ∀ᶠ n in atTop,
      walk a n ω / Real.sqrt (2 * n * Real.log (Real.log n)) ≤ 1 + 1 / (m : ℝ) := by
    rw [ae_all_iff]; intro m
    by_cases hm : 0 < m
    · exact (heps m hm).mono fun ω h _ => h
    · exact ae_of_all _ fun _ h => absurd h (by omega)
  filter_upwards [hae] with ω hω
  -- limsup F atTop = ⨅ n, ⨆ i ≥ n, F i ≤ 1.
  -- For each m ≥ 1: hω m gives ∃ N, ∀ i ≥ N, F i ≤ 1+1/m.
  -- So ⨆ i ≥ N, F i ≤ 1+1/m, hence ⨅ n, ⨆ i ≥ n, F i ≤ 1+1/m.
  -- Taking m → ∞: limsup ≤ 1.
  -- Need IsCoboundedUnder (· ≤ ·) atTop F for limsup_le_of_le.
  -- This requires a.s. F is not eventually ≤ -C for all C (i.e., walk doesn't
  -- IsCoboundedUnder: apply lil_upper_for_eps to neg_a (Rademacher by isRademacherSequence_neg_mul)
  -- to get ∀ᶠ n, -f n ≤ 1+1/m, i.e., f n ≥ -(1+1/m). Then any a with ∀ᶠ n, f n ≤ a
  -- must have a ≥ -(1+1/m), giving IsCoboundedUnder with b = -(1+1/1) = -2.
  -- Then limsup_le_of_le + Archimedean (hω gives limsup ≤ 1+1/m → limsup ≤ 1).
  -- The assembly uses lil_upper_for_eps + isRademacherSequence_neg_mul + limsup_le_of_le.
  sorry

end LIL

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
  intro Ω _ _ a _
  exact Filter.Eventually.of_forall fun ω n => ⟨
    max_le (walk_le_supNorm a n ω) (alternatingWalk_le_supNorm a n ω),
    -- Upper bound via Abel summation (Lemma 2 / Corollary 3)
    by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- n = 0: supNorm a 0 ω ≤ 0, and biSup over empty Icc is 0
      have hsup0 : supNorm a 0 ω ≤ 0 :=
        supNorm_le a 0 ω le_rfl (fun x _ => by simp [randomPoly])
      -- Helper: ⨆ (_ : k ∈ Finset.Icc 1 0), f k = 0 for each k (inner iSup over empty)
      have inner0 : ∀ (f : ℕ → ℝ) (k : ℕ),
          (⨆ (_ : k ∈ Finset.Icc 1 0), f k : ℝ) = 0 := by
        intro f k
        have : IsEmpty (k ∈ Finset.Icc 1 0) :=
          ⟨fun h => by simp at h⟩
        change sSup (Set.range fun (_ : k ∈ Finset.Icc 1 0) => f k) = 0
        rw [Set.range_eq_empty_iff.mpr this]; exact Real.sSup_empty
      -- Hence ⨆ k ∈ Finset.Icc 1 0, f k = 0 (outer iSup of constant 0)
      have bisup0 : ∀ (f : ℕ → ℝ), (⨆ k ∈ Finset.Icc 1 0, f k : ℝ) = 0 := by
        intro f; simp_rw [inner0]; exact ciSup_const
      rw [bisup0, bisup0, max_self]; exact hsup0
    · -- n ≥ 1: use abel_bound_nonneg
      -- BddAbove for the walk biSup
      have hbdd : BddAbove (Set.range fun k =>
          ⨆ (_ : k ∈ Finset.Icc 1 n), |walk a k ω|) := by
        refine ⟨∑ j ∈ Finset.Icc 1 n, |a j ω|, ?_⟩
        rintro z ⟨k, rfl⟩
        rcases em (k ∈ Finset.Icc 1 n) with hk | hk
        · haveI : Nonempty (k ∈ Finset.Icc 1 n) := ⟨hk⟩
          exact ciSup_le fun _ => by
            simp only [walk]
            exact (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum_of_subset_of_nonneg
                (fun j hj => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
                  le_trans (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hk).2⟩)
                (fun j _ _ => abs_nonneg _))
        · have : (Set.range fun (_ : k ∈ Finset.Icc 1 n) => |walk a k ω|) = ∅ :=
            Set.range_eq_empty_iff.mpr ⟨hk⟩
          simp [iSup, this]
          exact Finset.sum_nonneg fun j _ => abs_nonneg _
      -- |S_k| ≤ walk biSup for k ∈ Icc 1 n
      have hle_walk : ∀ k ∈ Finset.Icc 1 n, |walk a k ω| ≤
          ⨆ j ∈ Finset.Icc 1 n, |walk a j ω| := fun k hk =>
        (le_ciSup ⟨_, Set.forall_mem_range.mpr fun _ => le_rfl⟩ hk).trans
          (le_ciSup hbdd k)
      -- 0 ≤ walk biSup (since n ≥ 1, we have 1 ∈ Icc 1 n)
      have h0_walk : 0 ≤ ⨆ j ∈ Finset.Icc 1 n, |walk a j ω| :=
        le_trans (abs_nonneg _) (hle_walk 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩))
      -- Same for alternating walk (via walk of b_k = (-1)^k a_k)
      let b : ℕ → Ω → ℝ := fun j ω => (-1 : ℝ) ^ j * a j ω
      have hbdd_alt : BddAbove (Set.range fun k =>
          ⨆ (_ : k ∈ Finset.Icc 1 n), |walk b k ω|) := by
        refine ⟨∑ j ∈ Finset.Icc 1 n, |a j ω|, ?_⟩
        rintro z ⟨k, rfl⟩
        rcases em (k ∈ Finset.Icc 1 n) with hk | hk
        · haveI : Nonempty (k ∈ Finset.Icc 1 n) := ⟨hk⟩
          exact ciSup_le fun _ => by
            simp only [walk]
            calc |∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ j * a j ω|
                ≤ ∑ j ∈ Finset.Icc 1 k, |(-1 : ℝ) ^ j * a j ω| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ = ∑ j ∈ Finset.Icc 1 k, |a j ω| := by
                  congr 1; ext j; simp [abs_mul, abs_pow]
              _ ≤ ∑ j ∈ Finset.Icc 1 n, |a j ω| :=
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (fun j hj => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
                      le_trans (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hk).2⟩)
                    (fun j _ _ => abs_nonneg _)
        · have : (Set.range fun (_ : k ∈ Finset.Icc 1 n) => |walk b k ω|) = ∅ :=
            Set.range_eq_empty_iff.mpr ⟨hk⟩
          simp [iSup, this]
          exact Finset.sum_nonneg fun j _ => abs_nonneg _
      have hle_alt : ∀ k ∈ Finset.Icc 1 n, |walk b k ω| ≤
          ⨆ j ∈ Finset.Icc 1 n, |walk b j ω| := fun k hk =>
        (le_ciSup ⟨_, Set.forall_mem_range.mpr fun _ => le_rfl⟩ hk).trans
          (le_ciSup hbdd_alt k)
      have h0_alt : 0 ≤ ⨆ j ∈ Finset.Icc 1 n, |walk b j ω| :=
        le_trans (abs_nonneg _) (hle_alt 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩))
      -- Relate walk b to alternatingWalk
      have hwb : ∀ k, walk b k ω = alternatingWalk a k ω := fun k =>
        walk_neg_eq_alternatingWalk a k ω
      simp_rw [hwb] at hle_alt h0_alt
      -- Now apply supNorm_le
      apply supNorm_le a n ω (le_trans h0_walk (le_max_left _ _))
      intro x hx
      rcases le_or_gt 0 x with hx0 | hx0
      · -- x ∈ [0, 1]
        exact (abel_bound_nonneg a n ω hx0 hx.2 h0_walk hle_walk).trans (le_max_left _ _)
      · -- x ∈ [-1, 0)
        rw [show x = -(-x) from by ring, randomPoly_neg]
        exact (abel_bound_nonneg b n ω (by linarith) (by linarith [hx.1])
          h0_alt (by simp_rw [hwb] at hle_alt ⊢; exact hle_alt)).trans (le_max_right _ _)⟩

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

*Proof.* Endpoint reparametrization `x = ±e^{-u/n}` reduces `M_n / √n` to a
supremum over `u ≥ 0` of two random processes `Z_n^±(u)`. The 2D
Komlós–Major–Tusnády strong invariance principle (Lemma 13) couples these to
two independent copies of `Y` with error `Δ_n = O(log n / √n)`, which is
negligible at the `(log log n)^{1/3}` scale. The Gao–Li–Wellner small-deviation
asymptotics (Theorem 12) then give the small-ball probabilities for the
Gaussian limit, and a Borel–Cantelli argument on the sparse block-independent
subsequence `n_m` yields the dichotomy.

TODO: This sorry is a multi-year formalization project. It requires:
1. 2D Komlós–Major–Tusnády strong invariance principle (Lemma 13) — not in Mathlib;
   the 1D KMT coupling is itself a major open formalization target.
2. Gao–Li–Wellner small-deviation asymptotics for Y(u) = ∫₀¹ e^{-us} dB(s) — not in
   Mathlib; requires Karhunen–Loève expansion + entropy methods for Gaussian processes.
3. Borel–Cantelli on block-independent subsequences — the standard BC lemma is in
   Mathlib but the block-independence argument is custom.
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
  -- See TODO in docstring above.
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
  -- Open in mathematics: requires exact small-ball constant for Y(u) = ∫₀¹ e^{-us} dB(s),
  -- which is a major open problem in Gaussian-process small-ball theory (Remark 19,
  -- Chojecki 2026). Additionally requires full-sequence Borel–Cantelli (not just sparse).
  sorry

end Erdos524
