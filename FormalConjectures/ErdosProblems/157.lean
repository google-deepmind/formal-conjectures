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
import FormalConjecturesForMathlib.Combinatorics.Basic
import FormalConjecturesForMathlib.Combinatorics.Additive.Basis

/-!
# Erdős Problem 157

*Reference:* [erdosproblems.com/157](https://www.erdosproblems.com/157)

Erdős, Sárközy, and Sós asked whether there exists an infinite Sidon set that is also an
asymptotic basis of order 3. This was answered affirmatively by Pilatte.

[ESS94] Erdős, P., Sárközy, A. and Sós, V. T., *On sum sets of Sidon sets*. J. Number Theory
(1994).

[Er94b] Erdős, P., *Some of my favourite problems in various branches of combinatorics*.
Matematiche (Catania) (1994).

[Pi23] Pilatte, C., *Sidon sets are asymptotic bases of order 3*. (2023).
-/

open Filter Set

namespace Erdos157

/--
Erdős Problem 157 [ESS94, Er94b]:

Does there exist an infinite Sidon set which is an asymptotic basis of order $3$?

A set $A \subseteq \mathbb{N}$ is a Sidon set if all pairwise sums $a + b$ ($a, b \in A$)
are distinct. A set $A$ is an asymptotic basis of order $3$ if every sufficiently large
integer is the sum of $3$ elements from $A$.

Answered YES by Pilatte [Pi23].
-/
@[category research solved, AMS 5 11]
theorem erdos_157 :
    answer(True) ↔
      ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ Set.IsAsymptoticAddBasisOfOrder A 3 := by
  sorry

end Erdos157
