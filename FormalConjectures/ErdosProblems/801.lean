/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 801

*References:*
- [erdosproblems.com/801](https://www.erdosproblems.com/801)
- [Er79g] Erdős, Paul, *Some old and new problems in various branches of combinatorics*.
  Proceedings of the Tenth Southeastern Conference on Combinatorics, Graph Theory and Computing
  (Florida Atlantic Univ., Boca Raton, Fla., 1979) (1979), 19-37.
- [Al96b] Alon, Noga, *Independence numbers of locally sparse graphs and a Ramsey type problem*.
  Random Structures Algorithms (1996), 271-278.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos801

/--
If $G$ is a graph on $n$ vertices containing no independent set on $>n^{1/2}$ vertices then there
is a set of $\leq n^{1/2}$ vertices containing $\gg n^{1/2}\log n$ edges.

Proved by Alon [Al96b].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos801.lean#L1841"]
theorem erdos_801 : answer(True) ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n), (G.indepNum : ℝ) ≤ √n →
      ∃ S : Finset (Fin n), (S.card : ℝ) ≤ √n ∧
        c * √n * Real.log n ≤ (G.induce (S : Set (Fin n))).edgeSet.ncard := by
  sorry

end Erdos801
