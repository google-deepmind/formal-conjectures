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
# Erdős Problem 842

*Reference:* [erdosproblems.com/842](https://www.erdosproblems.com/842)

Let $G$ be a graph on $3n$ vertices formed by taking $n$ vertex disjoint triangles
and adding a Hamiltonian cycle (with all new edges) between these vertices.
Does $G$ have chromatic number at most $3$?

The answer is yes, proved by Fleischner and Stiebitz [FlSt92].

[Er92b] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Matematiche (Catania) 47 (1992), 231-240.

[FlSt92] Fleischner, H. and Stiebitz, M., _A solution to a colouring problem of P. Erdős_.
Discrete Math. 101 (1992), 39-48.
-/

open SimpleGraph

namespace Erdos842

/-- The graph of $n$ vertex-disjoint triangles on $3n$ vertices. Vertices $3i$, $3i+1$, $3i+2$
    form the $i$-th triangle. -/
def triangleGraph (n : ℕ) : SimpleGraph (Fin (3 * n)) where
  Adj u v := u ≠ v ∧ u.val / 3 = v.val / 3
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- A permutation $\sigma$ on `Fin m` is a single $m$-cycle (Hamiltonian cycle): applying $\sigma$
    repeatedly from any vertex can reach every other vertex. -/
def IsSingleCycle {m : ℕ} (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ u v : Fin m, ∃ k : ℕ, (σ ^ k) u = v

/-- The cycle graph induced by a permutation $\sigma$: vertices $u$ and $v$ are adjacent
    iff $\sigma(u) = v$ or $\sigma(v) = u$. -/
def cycleGraphOfPerm {m : ℕ} (σ : Equiv.Perm (Fin m)) : SimpleGraph (Fin m) where
  Adj u v := u ≠ v ∧ (σ u = v ∨ σ v = u)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/--
Erdős Problem 842 [Er92b]:

Let $G$ be a graph on $3n$ vertices formed by taking $n$ vertex-disjoint triangles
and adding a Hamiltonian cycle (with all new edges). Then $G$ has chromatic
number at most $3$.

Proved by Fleischner and Stiebitz [FlSt92].
-/
@[category research solved, AMS 5]
theorem erdos_842 : answer(True) ↔
    ∀ (n : ℕ), n ≥ 1 →
    ∀ (σ : Equiv.Perm (Fin (3 * n))),
    IsSingleCycle σ →
    (∀ u v : Fin (3 * n),
      (cycleGraphOfPerm σ).Adj u v → ¬(triangleGraph n).Adj u v) →
    (triangleGraph n ⊔ cycleGraphOfPerm σ).chromaticNumber ≤ 3 := by
  sorry

end Erdos842
