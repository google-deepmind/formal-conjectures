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

open MeasureTheory AddCircle Filter Topology Asymptotics Finset

/-!
# Erdős Problem 996

*Reference:*
 - [erdosproblems.com/996](https://www.erdosproblems.com/996)
 - [Er49d] Erdös, P. "On the strong law of large numbers." Transactions of the American Mathematical
    Society 67.1 (1949): 51-56.
 - [Ma66] Matsuyama, Noboru. "On the strong law of large numbers." Tohoku Mathematical Journal,
    Second Series 18.3 (1966): 259-269.
-/

/-- In [Er64b], a sequence of natural numbers `n 1 < n 2 < ...` is said to be lacunary if for all
`k`, `n (k + 1) / n k > c > 1`. -/
def Lacunary (n : ℕ → ℕ) : Prop := ∃ (c : ℝ), 1 < c ∧ ∀ k, c * (n k) < n (k + 1)

/-- `n k = 2 ^ k` is a lacunary sequence . -/
@[category test, AMS 40]
example : Lacunary (fun k => 2 ^ k) := by
  refine ⟨1.9, ⟨by linarith, fun n => ?_⟩⟩
  simp [pow_succ']
  linarith

/-- A lacunary sequence is strictly increasing. -/
@[category API, AMS 40]
lemma Lacunary.StrictMono {n : ℕ → ℕ} (hn : Lacunary n) : StrictMono n := by
  refine strictMono_nat_of_lt_succ fun k => (Nat.cast_lt (α := ℝ)).mp ?_
  obtain ⟨c, hc⟩ := hn
  by_cases h : n k = 0
  · simpa [h] using (hc.2 k)
  · calc
    _ < c * (n k) := (lt_mul_iff_one_lt_left (by simp [(n k).pos_iff_ne_zero.mpr h])).mpr hc.1
    _ < n (k + 1) := hc.2 k

noncomputable def fourierPartial {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 (@haarAddCircle T hT))
    (k : ℕ) : AddCircle T → ℂ :=
  fun x => ∑ i ∈ Icc (-(k : ℤ)) (k : ℤ), fourierCoeff f k • (fourier i x)

namespace Erdos996

/-- Does there exists a positive constant `ε` such that for all `f ∈ L²[0,1]` and all lacunary
sequences `n`, if `‖f - fₖ‖₂ = O(1 / log log log k) ^ ε`, then for almost every `x`,
`lim ∑ k ∈ Finset.range N, f ((n k) • x)) / N = ∫ t, f t ∂t`.-/
@[category research open, AMS 42]
theorem erdos_996.log3 : ∃ (ε : ℝ), 0 < ε ∧ ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    Lacunary n →
    (fun k => (eLpNorm (fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
    (fun k => 1 / (Real.log^[3] k) ^ ε)
    →
    ∀ᵐ x, Tendsto (fun N => (∑ k ∈ Finset.range N, f ((n k) • x)) / N) atTop
    (𝓝 (∫ t, f t ∂haarAddCircle)) := by
  sorry

/-- The following theorem is proved in [Ma66]. -/
@[category research solved, AMS 42]
theorem erdos_996.log2 : ∀ (ε : ℝ), 0.5 < ε →
    ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    Lacunary n →
    (fun k => (eLpNorm (fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
    (fun k => 1 / (Real.log^[2] k) ^ ε)
    →
    ∀ᵐ x, Tendsto (fun N => (∑ k ∈ Finset.range N, f ((n k) • x)) / N) atTop
    (𝓝 (∫ t, f t ∂haarAddCircle)) := by
  sorry

end Erdos996
