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
# Erdős Problem 916

*Reference:* [erdosproblems.com/916](https://www.erdosproblems.com/916)
-/

open SimpleGraph

namespace Erdos916

/-- `G` contains a cycle on `k ≥ 3` vertices and a vertex outside that cycle adjacent to at
least three vertices of the cycle. -/
def HasCycleWithTripleChord {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ (k : ℕ) (hk : 3 ≤ k) (c : Fin k → V) (v : V),
    Function.Injective c ∧
      (∀ i : Fin k, G.Adj (c i) (c (i + ⟨1, by omega⟩))) ∧
        v ∉ Set.range c ∧ 3 ≤ { i : Fin k | G.Adj v (c i) }.ncard

/--
Does every graph with $n$ vertices and $2n-2$ edges contain a cycle and another vertex adjacent to
three vertices on the cycle?
-/
@[category research open, AMS 5]
theorem erdos_916 :
    answer(sorry) ↔
      ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.edgeSet.ncard = 2 * n - 2 → HasCycleWithTripleChord G := by
  sorry

end Erdos916
