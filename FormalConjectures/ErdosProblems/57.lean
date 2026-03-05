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
# Erdős Problem 57

*Reference:* [erdosproblems.com/57](https://www.erdosproblems.com/57)

If $G$ is a graph with infinite chromatic number and $a_1 < a_2 < \cdots$ are the lengths
of its odd cycles, then $\sum 1/a_i = \infty$. Conjectured by Erdős and Hajnal [ErHa66],
proved by Liu and Montgomery [LiMo20].

[ErHa66] Erdős, P. and Hajnal, A., _On chromatic number of graphs and set-systems_, 1966.

[LiMo20] Liu, H. and Montgomery, R., _A solution to Erdős and Hajnal's odd cycle problem_, 2020.
-/

open SimpleGraph Finset

namespace Erdos57

/--
Erdős Problem 57 (Conjectured by Erdős-Hajnal [ErHa66], proved by Liu-Montgomery [LiMo20]):
If $G$ is a graph with infinite chromatic number and $a_1 < a_2 < \cdots$ are the lengths of
the odd cycles of $G$, then $\sum 1/a_i = \infty$.

We formalize "$\sum 1/a_i = \infty$" as: for any real bound $B$, there exists a finite set $T$
of odd natural numbers, each of which is the length of some cycle in $G$, whose reciprocals
sum to at least $B$.
-/
@[category research solved, AMS 5]
theorem erdos_57 {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ∀ (B : ℝ), ∃ (T : Finset ℕ),
      (∀ n ∈ T, Odd n ∧ ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = n) ∧
      B ≤ ∑ n ∈ T, (1 / (n : ℝ)) := by
  sorry

end Erdos57
