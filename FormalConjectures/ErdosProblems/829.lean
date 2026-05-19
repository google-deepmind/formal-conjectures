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
# Erdős Problem 829

*References:*
- [erdosproblems.com/829](https://www.erdosproblems.com/829)
- [Er83] Erdős, P. (1983), conjecture on the convolution of indicator functions of cubes.
-/

open Asymptotics Filter

namespace Erdos829

/--
The additive convolution of the indicator of the set of cubes with itself, evaluated at $n$.
This counts ordered pairs $(x, y) \in \mathbb{N} \times \mathbb{N}$ with $x^3 + y^3 = n$,
equivalently the number of representations of $n$ as a sum of two perfect cubes.
-/
noncomputable def r (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ^ 3 + p.2 ^ 3 = n}

/--
**Erdős Problem 829 (open).**  Let $A \subseteq \mathbb{N}$ be the set of perfect cubes.  Is
it true that $(1_A \ast 1_A)(n) \ll (\log n)^{O(1)}$?  That is, does there exist a natural
number $C$ such that the number of representations of $n$ as a sum of two cubes is
$O((\log n)^C)$ as $n \to \infty$?
-/
@[category research open, AMS 11]
theorem erdos_829 :
    answer(sorry) ↔
      ∃ C : ℕ, (fun n : ℕ => (r n : ℝ)) =O[atTop] (fun n : ℕ => (Real.log n) ^ C) := by
  sorry

end Erdos829
