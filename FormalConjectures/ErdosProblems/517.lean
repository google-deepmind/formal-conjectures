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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 517

*Reference:*
 - [erdosproblems.com/517](https://www.erdosproblems.com/517)
 - [Bi28] Biernacki, Miécislas, Sur les équations algébriques contenant des paramétres arbitraires.
    (1928), 145.
 - [Wa01] Wang, Yuefei. "On the Fatou set of an entire function with gaps." Tohoku Mathematical
    Journal, Second Series 53.1 (2001): 163-170.
-/

open Set Filter Topology

/-- This is the terminology adopted in [Wa01] and some other sources. -/
def hasFabryGaps (n : ℕ → ℕ) : Prop := StrictMono n ∧ Tendsto (fun k => n k / (k : ℝ)) atTop atTop

def hasFejerGaps (n : ℕ → ℕ) : Prop := StrictMono n ∧ Summable (fun k => 1 / (n k : ℝ))

@[category API, AMS 40]
theorem hasFejerGaps.hasFabryGaps {n : ℕ → ℕ} (hn : hasFejerGaps n) : hasFabryGaps n := by
  refine ⟨hn.1, ?_⟩
  simp only [tendsto_atTop, eventually_atTop, ge_iff_le]
  intro b
  /- use the Cauchy criterion of series. -/
  have : ∃ k > 0, ∀ m ≥ k, ∑ j : Icc ⌊m / 2⌋₊ m , 1 / (n j : ℝ)
    ≤ 1 / (2 * b) := by
    have : Icc (-1 / (2 * b)) (1 / (2 * b)) ∈ (𝓝 0) := by sorry
    obtain ⟨k, hk⟩ := hn.2.nat_tsum_vanishing this
    refine ⟨2 * k + 1, by linarith, fun m hm => ?_⟩
    have : Icc ⌊m / 2⌋₊ m ⊆ {n | k ≤ n} := by sorry
    have := (hk (Icc ⌊m / 2⌋₊ m) this).2
    simpa [tsum_fintype] using this
  obtain ⟨k, hk⟩ := this
  refine ⟨k, fun m hm => ?_⟩
  suffices m / n m ≤ 1 / b from by sorry
  calc
  _ ≤ 2 * ⌈m / 2⌉₊ / (n m : ℝ) := by sorry
  _ = 2 * ∑ j : Icc ⌊m / 2⌋₊ m, 1 / (n m : ℝ) := by sorry
  _ ≤ 2 * ∑ j : Icc ⌊m / 2⌋₊ m, 1 / (n j : ℝ) := by sorry
  _ ≤ 2 * 1 / (2 * b) := by grind
  _ = 1 / b := by grind

namespace Erdos517

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function such that `nₖ / k → ∞`, is it true that `f` assumes
every value infinitely often? -/
@[category research open, AMS 30]
theorem erdos_517.fabry {f : ℂ → ℂ} {n : ℕ → ℕ} (hn : hasFabryGaps n) {a : ℕ → ℂ}
    (hf : ∀ z, HasSum (fun k => (a k) * z ^ (n k)) (f z)) (z : ℂ) :
    {x : ℂ | f x = z}.Infinite := by
  sorry

/-- If `f(z) = ∑ aₖzⁿₖ` is an entire function such that `∑ 1 / nₖ < ∞`, then `f` assumes every value
infinitely often. This theorem is proved in [Bi28]. -/
@[category research solved, AMS 30]
theorem erdos_517.fejer {f : ℂ → ℂ} {n : ℕ → ℕ} (hn : hasFejerGaps n) {a : ℕ → ℂ}
    (hf : ∀ z, HasSum (fun k => (a k) * z ^ (n k)) (f z)) (z : ℂ) : {x : ℂ | f x = z}.Infinite :=
  sorry

end Erdos517
