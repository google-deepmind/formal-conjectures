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
# Erdős Problem 800

*References:*
- [erdosproblems.com/800](https://www.erdosproblems.com/800)
- [Al94] Alon, N., Subdivided graphs have linear Ramsey numbers. J. Graph Theory (1994), 343-347.
-/

@[expose] public section

namespace Erdos800

/--
If $G$ is a graph on $n$ vertices which has no two adjacent vertices of degree $\geq 3$ then
$$R(G)\ll n,$$
where the implied constant is absolute.

A problem of Burr and Erdős. Solved in the affirmative by Alon [Al94].
-/
@[category research solved, AMS 5]
theorem erdos_800 : answer(True) ↔
    ∃ C > (0 : ℝ), ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n →
      (∀ u v, G.Adj u v → ¬(3 ≤ G.degree u ∧ 3 ≤ G.degree v)) →
      (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ C * n := by
  sorry

-- TODO: Add variants of the problem.

end Erdos800
