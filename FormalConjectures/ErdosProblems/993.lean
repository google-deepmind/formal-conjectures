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
# Erdős Problem 993

*References:*
- [erdosproblems.com/993](https://www.erdosproblems.com/993)
- [AEMS87] Alavi, Y., Erdős, P., Malde, P. J., and Schwenk, A. J.,
  "The vertex independence sequence of a graph is not constrained",
  Congressus Numerantium 58 (1987), 15-23.
-/

open SimpleGraph

namespace Erdos993

/-- A sequence of natural numbers is unimodal if it weakly increases up to some index
and weakly decreases afterwards. -/
def IsUnimodal (f : ℕ → ℕ) : Prop :=
  ∃ m : ℕ, MonotoneOn f (Set.Iic m) ∧ AntitoneOn f (Set.Ici m)

/-- The number of independent sets of cardinality `k` in a finite simple graph. -/
def indepSetCount {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (G.indepSetFinset k).card

/--
The independent set sequence of every finite forest is unimodal.

Since a tree is an acyclic connected graph, this also covers the tree case.
-/
@[category research open, AMS 05]
theorem erdos_993
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) :
    IsUnimodal (indepSetCount G) := by
  sorry

end Erdos993
