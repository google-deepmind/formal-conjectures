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
import FormalConjecturesForMathlib.Combinatorics.Additive.Basis

/-!
# Erdős Problem 1147

Is the set of natural numbers $n \ge 1$ with $\lVert \alpha n^2 \rVert < 1 / \log n$ an additive
basis of order $2$ for every irrational $\alpha > 0$? Disproved by Konieczny.

*Reference:* [erdosproblems.com/1147](https://www.erdosproblems.com/1147)

[Va99] Vaughan, R.C., *The Hardy-Littlewood method*, 2nd edition, Cambridge University Press,
1997.

[Ko16b] Konieczny, J., *Sets of recurrence as bases for the positive integers*. Acta Arithmetica
(2016), 309–338.
-/

open Set Filter

namespace Erdos1147

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- The set $A(\alpha) = \{ n \ge 1 : \lVert \alpha n^2 \rVert < 1 / \log n \}$. -/
noncomputable def setA (α : ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ distNearestInt (α * (↑n) ^ 2) < 1 / Real.log (↑n)}

/-- The set $A(\alpha, \varepsilon) = \{ n \ge 1 : \lVert \alpha n^2 \rVert < \varepsilon(n) \}$
for a general threshold function $\varepsilon$. -/
noncomputable def setAGen (α : ℝ) (ε : ℕ → ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ distNearestInt (α * (↑n) ^ 2) < ε n}

/--
Erdős Problem 1147 [Va99, 1.21]:

Let $\alpha > 0$ be an irrational number. Is the set
$$A = \{ n \ge 1 : \lVert \alpha n^2 \rVert < 1 / \log n \},$$
where $\lVert \cdot \rVert$ denotes the distance to the nearest integer, an additive basis
of order $2$?

This was disproved by Konieczny [Ko16b]. In particular, for $\alpha = \sqrt{2}$,
the set $A$ is not an additive basis of order $2$.
-/
@[category research solved, AMS 11]
theorem erdos_1147 : answer(False) ↔
    ∀ α : ℝ, Irrational α → α > 0 →
      (setA α).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

/--
Generalization of Erdős Problem 1147 [Ko16b]:

For any function $\varepsilon(n) \to 0$, the set
$A = \{ n \ge 1 : \lVert \alpha n^2 \rVert < \varepsilon(n) \}$ is not an additive basis
of order $2$ for almost every $\alpha > 0$.
-/
@[category research solved, AMS 11]
theorem erdos_1147_general (ε : ℕ → ℝ) (hε : Tendsto (fun n => ε n) atTop (nhds 0)) :
    ∀ᵐ α : ℝ, α > 0 → ¬(setAGen α ε).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

end Erdos1147
