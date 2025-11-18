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
import Mathlib.Data.ENNReal.Basic

/-!
# Erdős Problem 1041

*Reference:* [erdosproblems.com/1041](https://www.erdosproblems.com/1041)
-/

open Polynomial MeasureTheory ENNReal

namespace Erdos1041

variable (n : ℕ) (f : ℂ[X]) (x : Fin n → ℂ)

/--
The length of a subset $s$ of $\mathbb{C}$ is defined to be its 1-dimensional
Hausdorff measure $\mathcal{H}^1(s)$.
-/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- Alternate definition using variation -/
noncomputable def length' {α : Type} [PseudoEMetricSpace α] {x y : α}
    (γ : Path x y) : ℝ≥0∞ :=
  eVariationOn γ Set.univ

/--
Let
$$ f(z) = \prod_{i=1}^{n} (z - z_i) \in \mathbb{C}[x] $$
with $|z_i| < 1$ for all $i$.

Conjecture: Must there always exist a path of length less than 2 in
$$ \{ z \in \mathbb{C} \mid |f(z)| < 1 \} $$
which connects two of the roots of $f$?
-/
@[category research open, AMS 32]
theorem erdos_1041
  (hn : n ≥ 2)
  (hx : ∀ i, ‖x i‖ < 1)
  (h : f = ∏ i : Fin n, (X - C (x i))) :
    ∃ (i j : Fin n) (hij : i ≠ j) (γ : Path (x i) (x j)),
    Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧
    length (Set.range γ) < 2 := by
  sorry

end Erdos1041
