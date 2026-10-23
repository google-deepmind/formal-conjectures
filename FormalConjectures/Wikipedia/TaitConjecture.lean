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
# Tait's conjecture

Tait (1884) conjectured that **every 3-connected planar cubic graph has a
Hamiltonian cycle**. He proposed it as a route to the four colour theorem (a
Hamiltonian cycle of such a graph yields a 4-edge/face colouring). The conjecture
is **false**: Tutte (1946) constructed a counterexample, the 46-vertex *Tutte
graph*, and smaller counterexamples (down to 38 vertices) are now known.

A graph is *cubic* (3-regular) if every vertex has degree `3`. It is
*3-connected* if it has more than `3` vertices and stays connected after deleting
any two vertices. Planarity is the combinatorial (Wagner) predicate
`SimpleGraph.IsPlanar` (no `K₅` and no `K₃,₃` minor), from
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Planar`.

A *Hamiltonian cycle* is a cycle visiting every vertex exactly once; we use
Mathlib's `SimpleGraph.IsHamiltonian` on a walk / `SimpleGraph.Walk.IsHamiltonianCycle`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Tait%27s_conjecture)
- P. G. Tait, *Listing's Topologie*, Philosophical Magazine (5th ser.) 17 (1884),
  30–46.
- W. T. Tutte, *On Hamiltonian circuits*, J. London Math. Soc. 21 (1946), 98–101.
  (The counterexample refuting the conjecture.)
-/

open SimpleGraph

namespace TaitConjecture

variable {V : Type*}

/-- A simple graph is *cubic* (3-regular) if every vertex has degree `3`. -/
def IsCubic [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, G.degree v = 3

/--
**Tait's conjecture (1884), refuted.** Every 3-connected planar cubic graph has a
Hamiltonian cycle.

This is stated as a `research solved` result because it is **false**: Tutte (1946)
gave a counterexample. The statement is phrased so that its falsity is the content
(the `answer` is `False`).
-/
@[category research solved, AMS 5]
theorem tait_conjecture :
    answer(False) ↔
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → (3 : ℕ) < n →
        (∀ s : Finset (Fin n), s.card = 2 → (G.induce ((s : Set (Fin n))ᶜ)).Connected) →
        IsCubic G → IsPlanar G →
        ∃ (v : Fin n) (p : G.Walk v v), p.IsHamiltonianCycle := by
  sorry

namespace variants

/--
**Tutte's counterexample (1946).** There is a 3-connected planar cubic graph with
no Hamiltonian cycle: the 46-vertex Tutte graph. This is the concrete witness that
refutes Tait's conjecture.
-/
@[category research solved, AMS 5]
theorem tutte_counterexample :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ (3 : ℕ) < n ∧
      (∀ s : Finset (Fin n), s.card = 2 → (G.induce ((s : Set (Fin n))ᶜ)).Connected) ∧
      IsCubic G ∧ IsPlanar G ∧
      ¬ ∃ (v : Fin n) (p : G.Walk v v), p.IsHamiltonianCycle := by
  sorry

end variants

end TaitConjecture
