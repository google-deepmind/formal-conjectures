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
# Erdős Problem 496

Erdős asked whether for every irrational α and every ε > 0 there exist positive integers x, y, z
with |x² + y² − z²α| < ε. This was proved by Margulis (1989) as a consequence of the Oppenheim
conjecture.

*Reference:* [erdosproblems.com/496](https://www.erdosproblems.com/496)
-/

namespace Erdos496

/--
Erdős Problem #496 (Oppenheim conjecture, proved by Margulis):
Let $\alpha \in \mathbb{R}$ be irrational and $\varepsilon > 0$. Then there exist positive integers
$x$, $y$, $z$ such that $|x^2 + y^2 - z^2 \alpha| < \varepsilon$.
-/
@[category research solved, AMS 11]
theorem erdos_496 (α : ℝ) (hα : Irrational α) (ε : ℝ) (hε : ε > 0) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      |((x : ℝ) ^ 2 + (y : ℝ) ^ 2 - (z : ℝ) ^ 2 * α)| < ε := by
  sorry

end Erdos496
