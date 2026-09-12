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
# Erdős Problem 1006

*Reference:* [erdosproblems.com/1006](https://www.erdosproblems.com/1006)
-/

open SimpleGraph

namespace Erdos1006

/-- An orientation of the edges of `G`, encoded as an irreflexive antisymmetric relation contained
in the adjacency relation, with exactly one direction for each undirected edge. -/
def IsOrientation {V : Type*} (G : SimpleGraph V) (R : V → V → Prop) : Prop :=
  (∀ a b, R a b → G.Adj a b) ∧
    (∀ a b, G.Adj a b → Xor (R a b) (R b a))

/-- `R` is acyclic: there is no finite directed cycle of length at least 3. -/
def IsAcyclicRel {V : Type*} (R : V → V → Prop) : Prop :=
  ∀ {n : ℕ} (p : Fin (n + 3) → V),
    (∀ i : Fin (n + 2), R (p i.castSucc) (p i.succ)) → ¬ R (p (Fin.last (n + 2))) (p 0)

/-- Reverse a single directed pair. -/
def reverseEdge {V : Type*} (R : V → V → Prop) (a b : V) : V → V → Prop :=
  fun x y => (R x y ∧ ¬ (x = a ∧ y = b)) ∨ (x = b ∧ y = a)

/--
Let $G$ be a graph with girth $>4$ (that is, it contains no cycles of length $3$ or $4$). Can the
edges of $G$ always be directed such that there is no directed cycle, and reversing the direction
of any edge also creates no directed cycle?
-/
@[category research open, AMS 5]
theorem erdos_1006 :
    answer(sorry) ↔
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        4 < G.egirth →
          ∃ R : V → V → Prop, IsOrientation G R ∧ IsAcyclicRel R ∧
            ∀ a b, R a b → IsAcyclicRel (reverseEdge R a b) := by
  sorry

end Erdos1006
