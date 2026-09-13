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

import FormalConjecturesUtil

/-!
# Erdős Problem 1031

*Reference:* [erdosproblems.com/1031](https://www.erdosproblems.com/1031)
-/

open SimpleGraph Real

namespace Erdos1031

/-- A subgraph induced by `S` is trivial if it is empty or complete. -/
def IsTrivialInduced {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) : Prop :=
  (G.induce S).edgeSet = ∅ ∨ (G.induce S).edgeSet = Set.univ

/--
If $G$ is a graph on $n$ vertices which contains no trivial (empty or complete) subgraph on
$\geq 10\log n$ many vertices, then must $G$ contain an induced non-trivial regular subgraph on
$\gg \log n$ many vertices?
-/
@[category research open, AMS 5]
theorem erdos_1031 :
    answer(sorry) ↔
      ∃ C > (0 : ℝ), ∀ n : ℕ, 1 < n →
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (∀ S : Set (Fin n), 10 * log n ≤ S.ncard → ¬ IsTrivialInduced G S) →
            ∃ T : Set (Fin n), C * log n ≤ T.ncard ∧
              ¬ IsTrivialInduced G T ∧
                ∃ d : ℕ, ∀ v ∈ T, (G.neighborSet v ∩ T).ncard = d := by
  sorry

end Erdos1031
