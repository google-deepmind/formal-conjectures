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
# Conjecture 1.74 (Minimal topological groups)

by V. P. Platonov

Describe all "minimal topological groups", that is, non-discrete Hausdorff
topological groups all of whose proper closed subgroups are discrete. The
minimal locally compact groups can be described without much effort, but the
problem is probably complicated in the general case.

A Tarski monster group equipped with a non-discrete Hausdorff group topology
is a minimal topological group in this sense, since all its proper subgroups
are finite (hence discrete in any Hausdorff group topology). Such topologizable
Tarski monsters exist by a theorem of Klyachko, Olshanskii and Osin.

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v40)
- A. A. Klyachko, A. Yu. Olshanskii, D. V. Osin, *On topologizable and
  non-topologizable groups*, Topology Appl. 160 (2013), 2104–2120,
  [arXiv:1210.7895](https://arxiv.org/abs/1210.7895), Theorem 1.4.
-/

namespace Kourovka.«1.74»

/--
A minimal topological group in Platonov's sense: a non-discrete Hausdorff
topological group all of whose proper closed subgroups are discrete.
-/
def IsMinimalTopologicalGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  IsTopologicalGroup G ∧ T2Space G ∧ ¬ DiscreteTopology G ∧
    ∀ H : Subgroup G, H ≠ ⊤ → IsClosed (H : Set G) → DiscreteTopology H

/--
Describe all minimal topological groups, that is, all non-discrete Hausdorff
topological groups whose proper closed subgroups are all discrete.
-/
@[category research open, AMS 20 22]
theorem kourovka_1_74 :
    ∀ (G : Type) [Group G] [TopologicalSpace G],
      IsMinimalTopologicalGroup G ↔
        (answer(sorry) : ∀ (G : Type) [Group G] [TopologicalSpace G], Prop) G := by
  sorry

/--
A Tarski monster group: an infinite group in which every non-trivial proper
subgroup has order a fixed prime $p$.
-/
def IsTarskiMonster (G : Type*) [Group G] : Prop :=
  Infinite G ∧ ∃ p : ℕ, p.Prime ∧
    ∀ H : Subgroup G, H ≠ ⊥ → H ≠ ⊤ → Nat.card H = p

/--
There exists a Tarski monster group that admits a non-discrete Hausdorff group
topology. This follows from Theorem 1.4 of Klyachko, Olshanskii and Osin, which
gives a topologizable Tarski monster of every sufficiently large odd exponent $n$;
taking $n$ to be a prime $p$ makes every non-trivial proper subgroup cyclic of
order $p$. Any such group is a minimal topological group.
-/
@[category research solved, AMS 20 22]
theorem kourovka_1_74.variants.tarski_monster : answer(True) ↔
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G),
      IsTarskiMonster G ∧ IsTopologicalGroup G ∧ T2Space G ∧
      ¬ DiscreteTopology G := by
  sorry

end Kourovka.«1.74»
