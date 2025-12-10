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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1080

*Reference:* [erdosproblems.com/1080](https://www.erdosproblems.com/1080)
-/

open SimpleGraph

namespace Erdos1080

/-- `IsBipartition G X Y` means that `X` and `Y` form a bipartition of the vertices of `G`. -/
def IsBipartition {V : Type*} (G : SimpleGraph V) (X Y : Set V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Set.univ ∧ ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ↔ v ∈ Y)

/--
Let $G$ be a bipartite graph on $n$ vertices such that one part has $\lfloor n^{2/3}\rfloor$
vertices. Is there a constant $c>0$ such that if $G$ has at least $cn$ edges then $G$ must
contain a $C_6$?
-/
@[category research open, AMS 5]
theorem erdos_1080 :
    (∃ (c : ℝ) (_ : c > 0), ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj] (n : ℕ) (_ : Fintype.card V = n) (_ : n > 0)
        (X Y : Set V) (_ : IsBipartition G X Y)
        (_ : X.ncard = ⌊(n : ℝ) ^ (2/3 : ℝ)⌋₊)
        (_ : Fintype.card G.edgeSet ≥ c * n),
        ∃ (v : V) (walk : G.Walk v v), walk.IsCycle ∧ walk.length = 6) ↔ answer(sorry) := by
  sorry

end Erdos1080
