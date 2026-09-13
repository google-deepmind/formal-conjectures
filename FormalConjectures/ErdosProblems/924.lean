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
# Erdős Problem 924

*Reference:* [erdosproblems.com/924](https://www.erdosproblems.com/924)
-/

open SimpleGraph

namespace Erdos924

/-- A `k`-edge-colouring of `G`. -/
abbrev EdgeColouring {V : Type*} (G : SimpleGraph V) (k : ℕ) :=
  G.edgeSet → Fin k

/-- The colouring has a monochromatic copy of `K_l`. -/
def HasMonoClique {V : Type*} (G : SimpleGraph V) {k l : ℕ}
    (c : EdgeColouring G k) : Prop :=
  ∃ (s : Finset V) (i : Fin k), s.card = l ∧
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b ∧
      ∀ he : s(a, b) ∈ G.edgeSet, c ⟨s(a, b), he⟩ = i

/--
Let $k\geq 2$ and $l\geq 3$. Is there a graph $G$ which contains no $K_{l+1}$ such that every
$k$-colouring of the edges of $G$ contains a monochromatic copy of $K_l$?
-/
@[category research open, AMS 5]
theorem erdos_924 :
    answer(sorry) ↔
      ∀ k ≥ 2, ∀ l ≥ 3,
        ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
          ¬ (⊤ : SimpleGraph (Fin (l + 1))).IsContained G ∧
            ∀ c : EdgeColouring G k, HasMonoClique (k := k) (l := l) G c := by
  sorry

end Erdos924
