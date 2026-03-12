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
import FormalConjectures.ErdosProblems.«58»

/-!
# Erdős Problem 57

*Reference:* [erdosproblems.com/57](https://www.erdosproblems.com/57)

If $G$ is a graph with infinite chromatic number and $a_1 < a_2 < \cdots$ are the lengths
of its odd cycles, then $\sum 1/a_i = \infty$. Conjectured by Erdős and Hajnal [ErHa66],
proved by Liu and Montgomery [LiMo20].

Erdős later asked ([Er81]) whether the odd cycle lengths must have positive upper density
among the odd numbers, a strictly stronger property. See also Problem 65 for a related
result on sums of reciprocals of all cycle lengths.

[ErHa66] Erdős, P. and Hajnal, A., _On chromatic number of graphs and set-systems_, 1966.

[LiMo20] Liu, H. and Montgomery, R., _A solution to Erdős and Hajnal's odd cycle problem_,
J. Amer. Math. Soc. 36 (2023), 1191-1234.
-/

open SimpleGraph Finset Erdos58

namespace Erdos57

/--
Erdős Problem 57 (Conjectured by Erdős-Hajnal [ErHa66], proved by Liu-Montgomery [LiMo20]):
If $G$ is a graph with infinite chromatic number and $a_1 < a_2 < \cdots$ are the lengths of
the odd cycles of $G$, then $\sum 1/a_i = \infty$.

We formalize "$\sum 1/a_i = \infty$" as: for any real bound $B$, there exists a finite set $T$
of odd cycle lengths of $G$ whose reciprocals sum to at least $B$.
-/
@[category research solved, AMS 5]
theorem erdos_57 {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ∀ (B : ℝ), ∃ (T : Finset ℕ),
      (∀ n ∈ T, n ∈ oddCycleLengths G) ∧
      B ≤ ∑ n ∈ T, (1 / (n : ℝ)) := by
  sorry

/--
Variant of Erdős Problem 57 (Erdős [Er81]):
If $G$ has infinite chromatic number, must the set of odd cycle lengths have positive
upper density among the odd numbers? This is strictly stronger than the reciprocal
divergence in `erdos_57`, since positive upper density implies divergence of reciprocals
but not conversely.
-/
@[category research open, AMS 5]
theorem erdos_57_positive_upper_density {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    0 < (oddCycleLengths G).upperDensity {n : ℕ | Odd n} := by
  sorry

end Erdos57
