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
# Erdős Problem 996

*References:*
 - [erdosproblems.com/996](https://www.erdosproblems.com/996)
 - [Er49d] Erdös, P. "On the strong law of large numbers." Transactions of the American Mathematical
    Society 67.1 (1949): 51-56.
 - [Ma66] Matsuyama, Noboru. "On the strong law of large numbers." Tohoku Mathematical Journal,
    Second Series 18.3 (1966): 259-269.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

noncomputable def fourierPartial {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 (@haarAddCircle T hT))
    (k : ℕ) : AddCircle T → ℂ :=
  fun x => ∑ i ∈ Icc (-k : ℤ) k, fourierCoeff f k • fourier i x

namespace Erdos996

/-- Does there exists a positive constant `C` such that for all `f ∈ L²[0,1]` and all lacunary
sequences `n`, if `‖f - fₖ‖₂ = O(1 / log log log k ^ C)`, then for almost every `x`,
`lim ∑ k ∈ Finset.range N, f (n k • x)) / N = ∫ t, f t ∂t`? -/
@[category research open, AMS 42]
theorem erdos_996 : answer(sorry) ↔
    ∃ (C : ℝ), 0 < C ∧ ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    IsLacunary n →
    (fun k => (eLpNorm (fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
    (fun k => 1 / (log (log (log k))) ^ C)
    →
    ∀ᵐ x, Tendsto (fun N => (∑ k ∈ .range N, f (n k • x)) / N) atTop
    (𝓝 (∫ t, f t ∂haarAddCircle)) := by
  sorry

/-- The following theorem is proved in [Ma66]. -/
@[category research solved, AMS 42]
theorem erdos_996.variants.log2 : ∀ (C : ℝ), 0.5 < C →
    ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    IsLacunary n →
    (fun k => (eLpNorm (fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
    (fun k => 1 / (log (log k)) ^ C)
    →
    ∀ᵐ x, Tendsto (fun N => (∑ k ∈ .range N, f (n k • x)) / N) atTop
    (𝓝 (∫ t, f t ∂haarAddCircle)) := by
  sorry

end Erdos996
