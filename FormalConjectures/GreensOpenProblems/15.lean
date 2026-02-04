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
# Green's Open Problem 15

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.15)
- [BJP14] T. Brown, V. Jungić and A. Poelstra, "On double 3-term arithmetic progressions",
  Integers 14 (2014), Paper No. A43.
- [CCS14] J. Cassaigne, J. D. Currie, L. Schaeffer and J. Shallit, "Avoidance of additive cubes and
  related results", Adv. in Appl. Math. 56 (2014), 25–66.
-/

open Set
open scoped NNReal

namespace Green15

/--
Does there exist a Lipschitz function $f : \mathbb{N} \to \mathbb{Z}$ whose graph
$\Gamma = \{(n, f(n)) : n \in \mathbb{N}\} \subseteq \mathbb{Z}^2$ is free of 3-term progressions?
-/
@[category research open, AMS 05 11]
theorem green_15 :
    answer(sorry) ↔ ∃ K : ℝ≥0, ∃ f : ℕ → ℤ, LipschitzWith K f ∧
      IsAPOfLengthFree { p : ℤ × ℤ | ∃ n : ℕ, p = (↑n, f n) } 3 := by
  sorry

/--
The answer is YES for 4-term progressions [BJP14].
-/
@[category research solved, AMS 05 11]
theorem green_15_ap4 :
    ∃ K : ℝ≥0, ∃ f : ℕ → ℤ, LipschitzWith K f ∧
      IsAPOfLengthFree { p : ℤ × ℤ | ∃ n : ℕ, p = (↑n, f n) } 4 := by
  sorry

-- TODO(jeangud) Add finitary version

end Green15
