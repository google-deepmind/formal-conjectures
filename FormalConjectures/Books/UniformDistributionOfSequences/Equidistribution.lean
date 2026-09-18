/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjecturesUtil
/-!
# Equidistributed Sequences

Corollary 4.2 of Chapter 1 states that the sequence $(x^n), n = 1, 2, ... ,$ is equidistributed modulo 1 for
almost all x > 1. And a little bit further down:
"one does not know whether sequences such as $(e^n)$, $(π^n)$, or even $((\frac 3 2)^n)$"
are equidistributed modulo 1 or not.

*References:*
  - [Uniform Distribution of Sequences](https://store.doverpublications.com/products/9780486149998)
by *L. Kuipers* and *H. Niederreiter*, 1974
  - [Wikipedia](https://en.wikipedia.org/wiki/Equidistributed_sequence)
  - [Mat80] de Mathan, Bernard. "Numbers contravening a condition in density modulo 1."
    Acta Mathematica Hungarica 36.3-4 (1980): 237-241.
  - [Pol79] Pollington, Andrew Douglas. "On the density of sequence $\{n_ {k}\xi\} $."
    Illinois Journal of Mathematics 23.4 (1979): 511-515.
-/

namespace Equidistribution

open scoped Topology

/--
A point `x` is an accumulation point of a sequence `s_0, s_1, ...`
if any neighbourhood of `x` contains a point of the sequence distinct
from `x`.
-/
def IsAccumulationPoint (x : ℝ) (s : ℕ → ℝ) : Prop :=
  x ∈ closure (Set.range s \ {x})

/--
If a point `x` is an accumulation point of a sequence `s_0, s_1, ...` then
there is a subsequence of `s` that tends to `x`
-/
@[category textbook, AMS 11 54]
theorem isAccumulationPoint_exists_subsequence_tendsto
    (x : ℝ) (s : ℕ → ℝ) (hx : IsAccumulationPoint x s) :
    ∃ (u : ℕ → ℕ), StrictMono u ∧ Filter.atTop.Tendsto (s ∘ u) (𝓝 x) := by
  refine MapClusterPt.tendsto_subseq (mapClusterPt_iff_frequently.2 fun U hU => ?_)
  rw [Filter.frequently_atTop]
  intro N
  by_contra hcon
  push Not at hcon
  -- Shrink `U` to exclude the finitely many values `s n ≠ x` with `n < N`.
  have hV : U ∩ ⋂ n ∈ Finset.range N, {y | s n ≠ x → y ≠ s n} ∈ 𝓝 x := by
    refine Filter.inter_mem hU ((Filter.biInter_finset_mem _).2 fun n _ => ?_)
    by_cases h : s n = x
    · exact Filter.mem_of_superset Filter.univ_mem fun y _ h' => absurd h h'
    · exact Filter.mem_of_superset (isOpen_compl_singleton.mem_nhds (Ne.symm h))
        fun y hy _ => hy
  obtain ⟨y, ⟨hyU, hyI⟩, ⟨n, rfl⟩, hyx⟩ := mem_closure_iff_nhds.1 hx _ hV
  rw [Set.mem_iInter₂] at hyI
  rcases Nat.lt_or_ge n N with hn | hn
  · exact hyI n (Finset.mem_range.2 hn) hyx rfl
  · exact hcon n hn hyU

/--
The sequence `(3/2)^n` is equidistributed modulo `1`.
-/
@[category research open, AMS 11]
theorem isEquidistributedModuloOne_three_halves_pow :
    IsEquidistributedModuloOne (fun n => (3 / 2 : ℝ)^n) := by
  sorry

/-- It is not true that for every transcendental number `x` the sequence `x * (3 / 2) ^ n` is
equidistributed modulo `1`. The sequence `(3 / 2) ^ n` is lacunary, so by the theorem of
Pollington [Pol79] and de Mathan [Mat80] the set of real numbers `x` for which `x * (3 / 2) ^ n`
is not even dense modulo `1` has Hausdorff dimension `1`. This set is uncountable, so it contains
transcendental numbers. Alternatively, an elementary nested-interval construction (see issue
#5003) gives a Cantor set of `x` with `Int.fract (x * (3 / 2) ^ (8 * j)) ∈ [0, 1 / 10]` for all
`j`, which already rules out equidistribution for uncountably many, hence some transcendental,
`x`. By Koksma's metric theorem (Kuipers–Niederreiter, Chapter 1, Section 4), the sequence
`x * (3 / 2) ^ n` is equidistributed modulo `1` for almost all `x`. -/
@[category research solved, AMS 11]
theorem isEquidistributedModuloOne_transcendental_three_halves_pow :
    ¬ ∀ x : ℝ, Transcendental ℚ x →
      IsEquidistributedModuloOne (fun n ↦ x * (3 / 2 : ℝ) ^ n) := by
  sorry

/--
The sequence `(3/2)^n` has infinitely many accumulation points modulo `1`.
-/
@[category research solved, AMS 11]
theorem isAccumulationPoint_three_halves_pow_infinite :
    {x | IsAccumulationPoint x (fun n => Int.fract <| (3 / 2 : ℝ)^n)}.Infinite := by
  sorry

/--
Find an accumulation point of the sequence `(3/2)^n` modulo `1`.
-/
@[category research open, AMS 11]
theorem isAccumulationPoint_three_halves_pow :
    IsAccumulationPoint answer(sorry) (fun n => Int.fract <| (3 / 2 : ℝ)^n) := by
  sorry

/-- The values of `(3/2)^n` modulo `1` are pairwise distinct: if `(3/2)^n - (3/2)^m` were an
integer for `m < n`, then `3^n - 3^m * 2^(n - m)` would be even. -/
@[category API, AMS 11]
theorem fract_three_halves_pow_injective :
    Function.Injective fun n : ℕ => Int.fract ((3 / 2 : ℝ) ^ n) := by
  intro n m hnm
  by_contra hne
  wlog hlt : m < n generalizing n m
  · exact this hnm.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) hne)
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 hnm
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have key : ((3 : ℤ) ^ n - 3 ^ m * 2 ^ (n - m) : ℤ) = z * 2 ^ n := by
    have : ((3 : ℝ) ^ n - 3 ^ m * 2 ^ (n - m)) = z * 2 ^ n := by
      have hm : (2 : ℝ) ^ n = 2 ^ m * 2 ^ (n - m) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      have e1 : (3 / 2 : ℝ) ^ n * 2 ^ n = 3 ^ n := by
        rw [div_pow, div_mul_cancel₀ _ h2]
      have e2 : (3 / 2 : ℝ) ^ m * 2 ^ n = 3 ^ m * 2 ^ (n - m) := by
        rw [hm, ← mul_assoc, div_pow, div_mul_cancel₀ _ (by positivity)]
      rw [← e1, ← e2, ← sub_mul, hz]
    exact_mod_cast this
  have hmod := congrArg (fun t : ℤ => (t : ZMod 2)) key
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hmod
  rw [show (2 : ZMod 2) = 0 from rfl, zero_pow (by omega), zero_pow (by omega),
    show (3 : ZMod 2) = 1 from rfl] at hmod
  simp at hmod

/--
There is an accumulation point of the sequence `(3/2)^n` modulo `1`: its values are pairwise
distinct and lie in `[0, 1]`, so they have an accumulation point by compactness.
-/
@[category test, AMS 11]
theorem isAccumulationPoint_three_halves_pow_exists :
    ∃ p, (IsAccumulationPoint p (fun n => Int.fract <| (3 / 2 : ℝ)^n)) := by
  have hinf : (Set.range fun n : ℕ => Int.fract ((3 / 2 : ℝ) ^ n)).Infinite :=
    Set.infinite_range_of_injective fract_three_halves_pow_injective
  have hsub : (Set.range fun n : ℕ => Int.fract ((3 / 2 : ℝ) ^ n)) ⊆ Set.Icc 0 1 := by
    rintro _ ⟨n, rfl⟩
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  obtain ⟨x, -, hx⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc hsub
  exact ⟨x, mem_closure_iff_clusterPt.2 (accPt_principal_iff_clusterPt.1 hx)⟩

end Equidistribution
