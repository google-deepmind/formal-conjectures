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
# Erdős Problem 1196

*Reference:* [erdosproblems.com/1196](https://www.erdosproblems.com/1196)

This file formalizes a conditional route to the corrected `1 + o(1)` upper bound
for primitive sets of natural numbers. The two deep analytic inputs are isolated
as separate statements about boundary mass.
-/

namespace Erdos1196

open scoped Asymptotics

-- TODO(Paul-Lez): add this to ForMathlib.

/--
A subset of a commutative monoid is primitive if divisibility between two
elements of the set can only occur between associated elements.
-/
def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y

open Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/- ## Definitions -/

/--
The boundary mass at a node `n` in the divisor recursion. It consists of the
source weight from small divisors `q < Y`, together with the weight from large
entry divisors `Y ≤ q` for which `n / q < X`.
-/
def bMass (X Y : ℕ) (n : ℕ) : ℝ :=
  if n < 2 then 0
  else 1 / ((n : ℝ) * (Real.log n) ^ 2) *
    ((n.divisors.filter (fun q => 0 < q ∧ q < Y)).sum (fun q => Λ q)
      + (n.divisors.filter (fun q => Y ≤ q ∧ n / q < X)).sum (fun q => Λ q))

/--
A natural-number version of primitiveness: no distinct elements of the set divide
one another.
-/
def IsPrimitiveNat (A : Set ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ∣ y → x = y

/-- On `ℕ`, associated elements are equal, so `IsPrimitive` implies `IsPrimitiveNat`. -/
@[category API, AMS 11]
lemma isPrimitive_implies_nat {A : Set ℕ} (h : IsPrimitive A) : IsPrimitiveNat A := by
  intro x hx y hy hxy
  simpa [associated_eq_eq] using h x hx y hy hxy

/- ## Proved analytic sub-lemmas -/

/-- Evaluate the integral of `1 / (x * (log x)^2)` over the interval `[K, N]`. -/
@[category API, AMS 11]
private lemma integral_inv_mul_logsq_eq (K N : ℕ) (hK : 2 ≤ K) (hKN : K ≤ N) :
    ∫ x in (K : ℝ)..N, (1 / (x * (Real.log x) ^ 2)) =
      -1 / Real.log N + 1 / Real.log K := by
  have hK_real : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKN_real : (K : ℝ) ≤ N := by exact_mod_cast hKN
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
  rotate_right
  use fun x => -1 / Real.log x
  · ring_nf
  · intro x hx
    convert HasDerivAt.div
      (hasDerivAt_const _ _)
      (Real.hasDerivAt_log <| show x ≠ 0 by
        cases Set.mem_uIcc.mp hx <;> linarith [hK_real, hKN_real])
      (ne_of_gt <| Real.log_pos <| show x > 1 by
        cases Set.mem_uIcc.mp hx <;> linarith [hK_real, hKN_real])
      using 1
    ring_nf
  · apply_rules [ContinuousOn.intervalIntegrable]
    exact continuousOn_of_forall_continuousAt fun x hx =>
      ContinuousAt.div continuousAt_const
        (ContinuousAt.mul continuousAt_id <|
          ContinuousAt.pow
            (Real.continuousAt_log <| by
              cases Set.mem_uIcc.mp hx <;> linarith [hK_real, hKN_real])
            _)
        (ne_of_gt <| mul_pos
          (by
            cases Set.mem_uIcc.mp hx <;> linarith [hK_real, hKN_real])
          (sq_pos_of_pos <| Real.log_pos <| by
            cases Set.mem_uIcc.mp hx <;> linarith [hK_real, hKN_real]))

/-- The first term in the integral comparison is bounded by `1 / log K`. -/
@[category API, AMS 11]
private lemma inv_mul_logsq_le_inv_log (K : ℕ) (hK : 2 ≤ K) :
    1 / ((K : ℝ) * (Real.log K) ^ 2) ≤ 1 / Real.log K := by
  have hK_real : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK_one : (1 : ℝ) ≤ K := by linarith [hK_real]
  gcongr
  · exact Real.log_pos <| Nat.one_lt_cast.mpr hK
  · have hlog_two := Real.log_two_gt_d9
    norm_num at hlog_two
    nlinarith [
      hK_real,
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) hK_real,
      mul_le_mul_of_nonneg_right hK_real (Real.log_nonneg hK_one)]

/-- Bound the summand at `n` by the integral over the unit interval `[n - 1, n]`. -/
@[category API, AMS 11]
private lemma inv_nat_logsq_le_integral_piece (K N n : ℕ) (hK : 2 ≤ K)
    (hn : n ∈ Finset.Icc (K + 1) N) :
    (1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
      ∫ x in (n - 1 : ℝ)..n, (1 / (x * (Real.log x) ^ 2)) := by
  have hn3Nat : 3 ≤ n := by
    linarith [Finset.mem_Icc.mp hn]
  have hn2Nat : 2 ≤ n := by linarith [hn3Nat]
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3Nat
  -- Since $1/(x (\log x)^2)$ is decreasing for $x \geq 2$, we have:
  have h_decreasing :
      ∀ x ∈ Set.Icc (n - 1 : ℝ) n,
        (1 / ((x : ℝ) * (Real.log x) ^ 2)) ≥
          (1 / ((n : ℝ) * (Real.log n) ^ 2)) := by
    intro x hx
    gcongr <;> norm_num at *
    · exact mul_pos
        (by
          linarith [show (n : ℝ) ≥ 3 by exact_mod_cast hn3Nat])
        (sq_pos_of_pos <| Real.log_pos <| by
          linarith [show (n : ℝ) ≥ 3 by exact_mod_cast hn3Nat])
    · linarith
    · exact Real.log_nonneg (by
        linarith [show (n : ℝ) ≥ 2 by exact_mod_cast hn2Nat])
    · linarith [show (n : ℝ) ≥ 2 by exact_mod_cast hn2Nat]
    · linarith
  refine le_trans ?_ (intervalIntegral.integral_mono_on ?_ ?_ ?_ h_decreasing) <;>
    norm_num
  apply_rules [ContinuousOn.intervalIntegrable]
  exact continuousOn_of_forall_continuousAt fun x hx =>
    ContinuousAt.mul
      (ContinuousAt.inv₀
        (ContinuousAt.pow
          (Real.continuousAt_log <| by
            cases Set.mem_uIcc.mp hx <;> linarith [hn3])
          _)
        (ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by
          cases Set.mem_uIcc.mp hx <;> linarith [hn3]))
      (ContinuousAt.inv₀ continuousAt_id <| ne_of_gt <| by
        cases Set.mem_uIcc.mp hx <;> linarith [hn3])

/--
The unit-interval integrals from `K + 1` to `N` combine into the integral over
`[K, N]`.
-/
@[category API, AMS 11]
private lemma sum_integral_inv_mul_logsq_adjacent (K N : ℕ) (hK : 2 ≤ K)
    (hKN : K ≤ N) :
    ∑ n ∈ Finset.Icc (K + 1) N,
        ∫ x in (n - 1 : ℝ)..n, (1 / (x * (Real.log x) ^ 2)) =
      ∫ x in (K : ℝ)..N, (1 / (x * (Real.log x) ^ 2)) := by
  have hK_real : (2 : ℝ) ≤ K := by exact_mod_cast hK
  erw [Finset.sum_Ico_eq_sum_range]
  convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num
  · ring_nf
  · rw [Nat.cast_sub] <;> push_cast <;> linarith
  · intro k hk
    apply_rules [ContinuousOn.intervalIntegrable]
    exact continuousOn_of_forall_continuousAt fun x hx =>
      ContinuousAt.mul
        (ContinuousAt.inv₀
          (ContinuousAt.pow
            (Real.continuousAt_log <| by
              cases Set.mem_uIcc.mp hx <;> linarith [hK_real])
            _)
          (ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by
            cases Set.mem_uIcc.mp hx <;> linarith [hK_real]))
        (ContinuousAt.inv₀ continuousAt_id <| ne_of_gt <| by
          cases Set.mem_uIcc.mp hx <;> linarith [hK_real])

/-- Bound the tail of the sum by the integral over `[K, N]`. -/
@[category API, AMS 11]
private lemma sum_inv_nat_logsq_tail_le_integral (K N : ℕ) (hK : 2 ≤ K)
    (hKN : K ≤ N) :
    ∑ n ∈ Finset.Icc (K + 1) N, (1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
      ∫ x in (K : ℝ)..N, (1 / (x * (Real.log x) ^ 2)) := by
  have h_piece_bound :
      ∀ n ∈ Finset.Icc (K + 1) N,
        (1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
          ∫ x in (n - 1 : ℝ)..n, (1 / (x * (Real.log x) ^ 2)) :=
    fun n hn => inv_nat_logsq_le_integral_piece K N n hK hn
  exact sum_integral_inv_mul_logsq_adjacent K N hK hKN ▸
    Finset.sum_le_sum h_piece_bound

/--
The sum of `1 / (n * (log n)^2)` over `n ∈ [K, N]` is at most `2 / log K`
when `K ≥ 2`.

The proof uses an integral comparison and the identity
`∫ dt / (t * (log t)^2) = -1 / log t`.
-/
@[category API, AMS 11]
lemma sum_inv_n_logsq_bound (K : ℕ) (hK : 2 ≤ K) (N : ℕ) :
    (Finset.Icc K N).sum (fun n => 1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
    2 / Real.log K := by
  by_cases hN : N < K
  · norm_num [Finset.Icc_eq_empty_of_lt hN]
    positivity
  · have hK_real : (2 : ℝ) ≤ K := by exact_mod_cast hK
    have hNK : K ≤ N := le_of_not_gt hN
    have hNK_real : (K : ℝ) ≤ N := by exact_mod_cast hNK
    have hK_one : (1 : ℝ) ≤ K := by linarith [hK_real]
    have hN_one : (1 : ℝ) ≤ N := by linarith [hK_one, hNK_real]
    have h_integral_comparison :
        ∑ n ∈ Finset.Icc K N, (1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
          1 / ((K : ℝ) * (Real.log K) ^ 2) +
            ∫ x in (K : ℝ)..N, (1 / (x * (Real.log x) ^ 2)) := by
      have h_tail_bound :
          ∑ n ∈ Finset.Icc (K + 1) N, (1 / ((n : ℝ) * (Real.log n) ^ 2)) ≤
            ∫ x in (K : ℝ)..N, (1 / (x * (Real.log x) ^ 2)) :=
        sum_inv_nat_logsq_tail_le_integral K N hK hNK
      erw [Finset.sum_Ico_eq_sub _] at * <;> norm_num [Finset.sum_range_succ] at *
      · linarith
      · lia
      · linarith
    have h_integral_eval := integral_inv_mul_logsq_eq K N hK hNK
    have h_bound := inv_mul_logsq_le_inv_log K hK
    ring_nf at *
    linarith [
      inv_nonneg.2 (Real.log_nonneg hK_one),
      inv_nonneg.2 (Real.log_nonneg hN_one)]

/--
`bMass` is bounded by the crude bound `1/(n log n)` using the
von Mangoldt divisor sum identity `∑_{q | n} Λ(q) = log n`.
-/
@[category API, AMS 11]
lemma bMass_le_crude (X Y n : ℕ) (hn : 2 ≤ n) :
    bMass X Y n ≤ 1 / ((n : ℝ) * Real.log n) := by
  unfold bMass
  split_ifs <;> norm_num
  · linarith
  · -- By definition of the von Mangoldt function, `∑_{q | n} Λ(q) = log n`.
    have h_von_mangoldt : ∑ q ∈ n.divisors, Λ q = Real.log n :=
      ArithmeticFunction.vonMangoldt_sum
    -- The two filtered sums are nonnegative sub-sums of the full divisor sum.
    have h_simplify :
        (∑ q ∈ n.divisors.filter (fun q => 0 < q ∧ q < Y), Λ q) +
            (∑ q ∈ n.divisors.filter (fun q => Y ≤ q ∧ n / q < X), Λ q) ≤
          ∑ q ∈ n.divisors, Λ q := by
      rw [← Finset.sum_union]
      · exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
          fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith
    convert mul_le_mul_of_nonneg_left h_simplify
      (show 0 ≤ (Real.log n ^ 2)⁻¹ * (n : ℝ)⁻¹ by positivity) using 1
    · ring_nf
      grind

/- ## Core lemmas requiring deep number-theoretic estimates -/

/--
Analytic bound on the total boundary mass.

For each `Y ≥ 2`, there is a constant `C > 0` such that every interval `[X, N]`
with `X ≥ 2` has total boundary mass at most `1 + C / log X`.

The expected proof splits the mass into small prime-power divisors and entry
nodes. The entry-node estimate uses Mertens-type tail bounds for
`∑ Λ(q) / (q * (log (m * q))^2)`, together with a harmonic-sum estimate. These
analytic estimates are not currently available in Mathlib.
-/
@[category API, AMS 11]
lemma bMass_partial_sum_bound (Y : ℕ) (hY : 2 ≤ Y) :
    ∃ C : ℝ, C > 0 ∧ ∀ (X : ℕ), 2 ≤ X → ∀ (N : ℕ),
    (Finset.Icc X N).sum (fun n => bMass X Y n) ≤ 1 + C / Real.log X := by
  sorry

/--
Finite primitive-set bound using the divisor recursion.

For a finite primitive set `F ⊆ [X, ∞)`, the logarithmic sum over `F` is bounded
by the boundary mass up to `F.sup id`.

The intended proof assigns hit weights to divisors `n | a` with `X ≤ n ≤ a`,
shows that the weighted boundary mass recovers `1 / (a * log a)`, and then
proves the combined hit weight is at most `1` by reverse induction. The final
transition-mass estimate again depends on Mertens-type input.
-/
@[category API, AMS 11]
lemma finite_primitive_sum_le_bMass (X Y : ℕ) (hX : 2 ≤ X) (hY : 2 ≤ Y)
    (F : Finset ℕ) (hF : ∀ a ∈ F, X ≤ a)
    (hprim : IsPrimitiveNat (F : Set ℕ)) :
    F.sum (fun a => 1 / ((a : ℝ) * Real.log a)) ≤
    (Finset.Icc X (F.sup _root_.id)).sum (fun n => bMass X Y n) := by
  sorry

/--
Bound the infinite sum over a set by a uniform bound on all finite subsums.

This uses nonnegativity of the summand and the fact that the `tsum` of a
nonnegative real-valued function is controlled by its finite partial sums.
-/
@[category API, AMS 11]
lemma tsum_le_of_finite_sums_le {A : Set ℕ} (hA : A ⊆ Set.Ici 2) (B : ℝ)
    (hB : ∀ F : Finset ℕ, ↑F ⊆ A →
      F.sum (fun a => 1 / ((a : ℝ) * Real.log a)) ≤ B) :
    ∑' (a : A), (1 / ((a.val : ℝ).log * (a.val : ℝ))) ≤ B := by
  have hSummable : Summable (fun a : A => 1 / ((a : ℝ) * Real.log a)) := by
    refine summable_of_sum_le (c := B) ?_ ?_
    · exact fun x => one_div_nonneg.2 <| mul_nonneg (Nat.cast_nonneg _) <|
        Real.log_nonneg <| Nat.one_le_cast.2 <| by
          linarith [Set.mem_Ici.1 <| hA x.2]
    · intro u
      convert hB (u.image Subtype.val) (by aesop) using 1
      rw [Finset.sum_image]
      simp
  refine le_of_tendsto_of_tendsto' (by simpa [mul_comm] using hSummable.hasSum)
    tendsto_const_nhds ?_
  intro F
  convert hB (F.image Subtype.val) (by aesop) using 1
  · rw [Finset.sum_image]
    · simp [mul_comm]
    · intro a _ b _ h
      exact Subtype.ext h

/- ## Main quantitative bound -/

/--
The main quantitative estimate for sets contained in `[X, ∞)`: there is an
absolute constant `C > 0` such that every primitive set `A ⊆ [X, ∞)` satisfies
`∑' a, 1 / (a * log a) ≤ 1 + C / log X`.
-/
@[category API, AMS 11]
theorem primitive_set_quantitative_bound' :
    ∃ C : ℝ, C > 0 ∧ ∀ (X : ℕ), 2 ≤ X →
    ∀ (A : Set ℕ), A ⊆ Set.Ici X → IsPrimitive A →
    ∑' (a : A), (1 / ((a.val : ℝ).log * (a.val : ℝ))) ≤ 1 + C / Real.log X := by
  obtain ⟨C, hCpos, hbnd⟩ := bMass_partial_sum_bound 2 le_rfl
  refine ⟨C, hCpos, fun X hX A hA hprim => ?_⟩
  have hA2 : A ⊆ Set.Ici 2 := fun a ha => le_trans hX (hA ha)
  apply tsum_le_of_finite_sums_le hA2
  intro F hFA
  have hFX : ∀ a ∈ F, X ≤ a := fun a ha => hA (hFA ha)
  have hFprim : IsPrimitiveNat (F : Set ℕ) :=
    fun x hx y hy hxy => isPrimitive_implies_nat hprim x (hFA hx) y (hFA hy) hxy
  calc F.sum (fun a => 1 / ((a : ℝ) * Real.log a))
      ≤ (Finset.Icc X (F.sup _root_.id)).sum (fun n => bMass X 2 n) :=
        finite_primitive_sum_le_bMass X 2 hX le_rfl F hFX hFprim
    _ ≤ 1 + C / Real.log X := hbnd X hX (F.sup _root_.id)

end

/--
A strict version of `primitive_set_quantitative_bound'`, obtained by increasing
the constant.
-/
@[category API, AMS 11]
lemma primitive_set_quantitative_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ (X : ℕ), 2 ≤ X →
    ∀ (A : Set ℕ), A ⊆ Set.Ici X → IsPrimitive A →
    ∑' (a : A), (1 / ((a.val : ℝ).log * (a.val : ℝ))) < 1 + C / Real.log X := by
  obtain ⟨C, hC, hC'⟩ := primitive_set_quantitative_bound'
  use C + 1
  constructor
  · linarith
  · intro X hX A hA hA'
    refine lt_of_le_of_lt (hC' X hX A hA hA') ?_
    rw [add_lt_add_iff_left, div_lt_div_iff_of_pos_right]
    · linarith
    · have hX' : (1 : ℝ) < X := by
        exact_mod_cast lt_of_lt_of_le Nat.one_lt_two hX
      exact Real.log_pos hX'

/- ## Deducing the corrected `1 + o(1)` statement -/

/-- A constant divided by `log (max 2 x)` tends to zero as `x → ∞`. -/
@[category API, AMS 11]
private lemma tendsto_const_div_log_atTop (C : ℝ) :
    Tendsto (fun x : ℕ => C / Real.log (max 2 (x : ℝ))) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp <|
    Filter.tendsto_atTop_atTop.mpr fun x => ⟨⌈x⌉₊ + 1, fun n hn =>
      le_trans (le_of_lt <| Nat.lt_of_ceil_lt hn) <| le_max_right _ _⟩

/-- A primitive subset of `ℕ` containing `1` is exactly `{1}`. -/
@[category API, AMS 11]
private lemma isPrimitive_singleton_one
    (A : Set ℕ) (hprim : IsPrimitive A) (h1 : (1 : ℕ) ∈ A) :
    A = {1} := by
  ext x
  constructor
  · intro hx
    have hx_eq : (1 : ℕ) = x := by
      simpa [associated_eq_eq] using hprim 1 h1 x hx (one_dvd x)
    exact hx_eq.symm
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact h1

/--
For every positive `x`, primitive sets of natural numbers contained in
`[x, ∞)` satisfy the corrected Erdős bound
`∑' a, 1 / (a * log a) < 1 + o(1)` as `x → ∞`.
-/
@[category research solved, AMS 11]
theorem erdos_1196 :
    ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
    ∀ (x : ℕ), x > 0 → ∀ A ⊆ Set.Ici x, IsPrimitive A →
      ∑' (a : A), (1 / ((a.val : ℝ).log * (a.val : ℝ))) < 1 + o x := by
  obtain ⟨C, hCpos, hbound⟩ := primitive_set_quantitative_bound
  refine ⟨fun x => C / Real.log (max 2 (x : ℝ)), ?_, ?_⟩
  · rw [show (1 : ℕ → ℝ) = fun _ => (1 : ℝ) from rfl, Asymptotics.isLittleO_one_iff]
    exact tendsto_const_div_log_atTop C
  · intro x hx A hA hprim
    by_cases hx2 : 2 ≤ x
    · have hx2' : (2 : ℝ) ≤ x := by exact_mod_cast hx2
      simpa [max_eq_right hx2'] using hbound x hx2 A hA hprim
    · have hx1 : x = 1 := by omega
      subst hx1
      by_cases h1 : (1 : ℕ) ∈ A
      · have hA1 := isPrimitive_singleton_one A hprim h1
        rw [hA1]
        simp [Real.log_one]
        positivity
      · have hA2 : A ⊆ Set.Ici 2 := by
          intro a ha
          have h := hA ha
          simp [Set.mem_Ici] at h ⊢
          have : a ≠ 1 := by
            rintro rfl
            exact h1 ha
          omega
        simpa [Nat.cast_one, max_eq_left (by norm_num : (2 : ℝ) ≥ 1)]
          using hbound 2 le_rfl A hA2 hprim

end Erdos1196
