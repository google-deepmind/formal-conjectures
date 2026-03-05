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
# Erdős Problem 58

*Reference:* [erdosproblems.com/58](https://www.erdosproblems.com/58)

Conjectured by Bollobás and Erdős. Bollobás and Shelah confirmed it for $k = 1$.
Proved by Gyárfás [Gy92], who showed the stronger result that if $G$ is 2-connected,
then $G$ is either $K_{2k+2}$ or contains a vertex of degree at most $2k$.

[Gy92] Gyárfás, A., *Graphs with $k$ odd cycle lengths*, Discrete Mathematics 103 (1992), 41–48.
-/

open SimpleGraph

namespace Erdos58

/-- The set of lengths of odd cycles in a graph $G$. -/
def oddCycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {n : ℕ | Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/--
**Erdős Problem 58** (Bollobás–Erdős conjecture, proved by Gyárfás [Gy92]):

If $G$ is a finite graph containing odd cycles of at most $k$ different lengths,
then $\chi(G) \leq 2k + 2$, with equality if and only if $G$ contains $K_{2k+2}$ as a
clique subgraph.
-/
@[category research solved, AMS 5]
theorem erdos_58 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : (oddCycleLengths G).ncard ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ) ∧
    (G.chromaticNumber = (2 * k + 2 : ℕ) ↔ ∃ s : Finset V, G.IsNClique (2 * k + 2) s) := by
  sorry

end Erdos58
