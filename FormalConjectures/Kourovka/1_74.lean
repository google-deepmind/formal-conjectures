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
# Conjecture 1.74 (Tarski monster topologizability)

by V. P. Platonov

Problem 1.74 asks to describe all "minimal topological groups" in Platonov's
sense: non-discrete Hausdorff topological groups all of whose proper closed
subgroups are discrete. A natural test case: does there exist a Tarski monster
group admitting a non-discrete Hausdorff group topology? A Tarski monster
would be a minimal group in this sense, since all its proper subgroups are
finite (hence discrete in any Hausdorff group topology).

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v40)
-/

namespace Kourovka.«1.74»

/--
A Tarski monster group: an infinite group in which every non-trivial proper
subgroup has order a fixed prime $p$.
-/
def IsTarskiMonster (G : Type*) [Group G] : Prop :=
  Infinite G ∧ ∃ p : ℕ, p.Prime ∧
    ∀ H : Subgroup G, H ≠ ⊥ → H ≠ ⊤ → Nat.card H = p

/--
Does there exist a Tarski monster group that admits a non-discrete Hausdorff
group topology?
-/
@[category research open, AMS 20 22]
theorem kourovka.«1.74» : answer(sorry) ↔
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G),
      IsTarskiMonster G ∧ IsTopologicalGroup G ∧ T2Space G ∧
      ¬ DiscreteTopology G := by
  sorry

end Kourovka.«1.74»
