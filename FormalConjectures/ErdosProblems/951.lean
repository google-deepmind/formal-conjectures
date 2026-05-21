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
# Erdős Problem 951

*References:*
 - [erdosproblems.com/951](https://www.erdosproblems.com/951)
 - [Er77c] Erdős, Paul, Problems and results on combinatorial number theory. III. Number theory day (Proc. Conf., Rockefeller Univ.,
    New York, 1976) (1977), 43-72.
-/

open scoped Finsupp Nat.Prime Topology
open Filter

namespace Erdos951

/-- A sequence `a : ℕ → ℝ` is said to have property `Erdos951Prop` if for any pair of distinct
finitely supported sequences `k l : ℕ →₀ ℕ` their corresponding Beurling integers are of distance
at least one apart. -/
def Erdos951Prop (a : ℕ → ℝ) : Prop :=
  ∀ (k ℓ : ℕ →₀ ℕ), k ≠ ℓ → |beurlingInteger a k - beurlingInteger a ℓ| ≥ 1

/-- If `a` has property `Erdos951Prop` and `1 < a 0`, then `a` is a set of Beurling
prime numbers. -/
@[category API, AMS 11]
theorem erdos_951.variants.isBeurlingPrimes {a : ℕ → ℝ} (ha : 1 < a 0)
    (hm : StrictMono a) (he : Erdos951Prop a) :
    IsBeurlingPrimes a := by
  refine ⟨ha, hm, tendsto_atTop_atTop.2 fun x => ?_⟩
  by_contra h_contra
  obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto a Filter.atTop (𝓝 L) :=
    ⟨_, tendsto_atTop_isLUB hm.monotone (isLUB_ciSup ⟨x, Set.forall_mem_range.2 fun n =>
    le_of_not_ge fun hn => h_contra ⟨n, fun m hm' => hn.trans (hm.monotone hm')⟩⟩)⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hL (1 / 2) (by norm_num)
  have := hm (by linarith : N < N + 1)
  have h_diff : a (N + 1) - a N ≥ 1 := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ a _ - _)]
    simpa using he (.single (N + 1) 1) (.single N 1) (by simpa [Finsupp.ext_iff] using ⟨N, by simp⟩)
  linarith [abs_lt.1 (hN N le_rfl), abs_lt.1 (hN (N + 1) (by grind))]

/-- If `1 < a 0 < ...` has property `Erdos951Prop`, is it true that `#{a i ≤ x} ≤ π x`? -/
@[category research open, AMS 11]
theorem erdos_951 : answer(sorry) ↔
    ∀ a : ℕ → ℝ, 1 < a 0 → StrictMono a → Erdos951Prop a →
      ∀ᶠ (x : ℝ) in Filter.atTop, {i : ℕ | a i ≤ x}.ncard ≤ π ⌊x⌋₊ := by
  sorry

/-- Beurling conjectured that if the number of Beurling integer in `[1, x]`
is `x + o(log x)`, then `a` must be the sequence of primes. -/
@[category research solved, AMS 11]
theorem erdos_951.variants.beurling :
    ∀ a : ℕ → ℝ, IsBeurlingPrimes a →
    ((fun x => (BeurlingIntegers a ∩ .Iic x).ncard - x) =o[atTop] Real.log) →
    a = Nat.cast ∘ Nat.nth Nat.Prime := by
  sorry

end Erdos951
