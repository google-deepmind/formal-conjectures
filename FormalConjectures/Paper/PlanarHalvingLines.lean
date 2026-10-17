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
# A power saving for planar halving lines

*Reference:* OpenAI, *A power saving for planar halving lines* (2026).
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf
-/

@[expose] public section

namespace PlanarHalvingLines

/-- The signed determinant that determines which side of a line a point lies on. -/
def orient (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- Distinct indexed points with no three collinear. -/
def GeneralPosition {n : ℕ} (P : Fin n → ℝ × ℝ) : Prop :=
  Function.Injective P ∧ ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    orient (P i) (P j) (P k) ≠ 0

/-- The number of indexed points strictly to the left of an oriented line. -/
noncomputable def sideCount {n : ℕ} (P : Fin n → ℝ × ℝ) (i j : Fin n) : ℕ :=
  (Finset.univ.filter fun k => 0 < orient (P i) (P j) (P k)).card

/-- The number of unordered pairs whose line leaves equally many points on each side. -/
noncomputable def halvingCount {n : ℕ} (P : Fin n → ℝ × ℝ) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ sideCount P ij.1 ij.2 = (n - 2) / 2 ∧
      sideCount P ij.2 ij.1 = (n - 2) / 2).card

/-- A point on the defining line contributes zero orientation. -/
@[category test, AMS 52]
theorem orient_self (p q : ℝ × ℝ) : orient p q p = 0 := by
  simp [orient]

/-- There is an absolute $\varepsilon > 0$ such that every sufficiently large even
set of $n$ planar points in general position has at most $Cn^{4/3-\varepsilon}$ halving pairs.
The even-order restriction makes the two side counts equal. -/
@[category research solved, AMS 5 52,
  formal_proof using lean4 at "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/HalvingLines/Main.lean#L27"]
theorem halving_count_power_saving :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∃ n₀ : ℕ,
      ∀ n : ℕ, Even n → n₀ ≤ n → ∀ P : Fin n → ℝ × ℝ,
        GeneralPosition P → (halvingCount P : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε) := by
  sorry

end PlanarHalvingLines
