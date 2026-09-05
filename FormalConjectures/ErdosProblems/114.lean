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
# Erdős Problem 114

*Reference:* [erdosproblems.com/114](https://www.erdosproblems.com/114)

If $p(z) \in \mathbb{C}[z]$ is a monic polynomial of degree $n$, is the length
of the curve $\{z \in \mathbb{C} : |p(z)| = 1\}$ maximised when
$p(z)=z^n-1$?

Erdős, Herzog, and Piranian [EHP58] asked this problem.  Eremenko and Hayman
[ErHa99] proved the conjecture for $n=2$.  Tao [Ta25] proved that
$p(z)=z^n-1$ is the unique maximiser, up to rotation and translation, for all
sufficiently large $n$.
-/

open Polynomial MeasureTheory ENNReal Classical

namespace Erdos114

/-- The level-1 lemniscate of a complex polynomial `p`. -/
def levelCurveUnit (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ = 1}

/-- The length of a subset of `ℂ`, represented as its one-dimensional
Hausdorff measure. -/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ :=
  μH[1] s

/-- The length of the level-1 lemniscate of `p`. -/
noncomputable def lemniscateLength (p : ℂ[X]) : ℝ≥0∞ :=
  length (levelCurveUnit p)

/-- **Erdős Problem 114** (open conjecture).  Among monic complex polynomials
of degree $n$, $z^n - 1$ maximizes the length of the level-$1$ lemniscate.

This is the all-degree conjecture and remains open. -/
@[category research open, AMS 30]
theorem erdos_114 (n : ℕ) (hn : 1 ≤ n)
    (p : ℂ[X]) (hp : p.Monic) (hp_deg : p.natDegree = n) :
    lemniscateLength p ≤ lemniscateLength (X ^ n - C (1 : ℂ)) := by
  sorry

end Erdos114
