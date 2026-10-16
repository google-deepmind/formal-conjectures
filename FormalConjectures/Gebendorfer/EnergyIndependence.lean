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
module

public import FormalConjecturesUtil

/-!
# Uniform energy–independence separation for imperfect graphs

*References:*
- [J. J. Gebendorfer, Uniform energy–independence separation for imperfect graphs, 21 September 2026, Theorem 1.1; manuscript and intake](https://github.com/google-deepmind/formal-conjectures/issues/7241)
- [H. Kumar, S. Pragada, underlying energy inequality, Theorem 1.2](https://arxiv.org/abs/2607.19817v1)
- [S. A. Mojallal, equality classification, Theorem 1.3](https://arxiv.org/abs/2608.04367v1)

This is Gebendorfer's proposed uniform strengthening. The inequality and equality
classification in the other references are credited dependencies. The domain
includes disconnected graphs; positivity for each graph is weaker than this claim.
-/

@[expose] public section
namespace Gebendorfer.EnergyIndependence
open SimpleGraph

/-- Adjacency energy with eigenvalues counted with their algebraic multiplicities. -/
noncomputable def energy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|

/-- An induced subgraph has different chromatic and clique numbers. -/
def IsImperfect {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ A : Finset V, (G.induce (A : Set V)).chromaticNumber ≠
    ((G.induce (A : Set V)).cliqueNum : ℕ∞)

/-- There is one absolute positive real gap for all finite simple imperfect
graphs, independent of their orders. Energy is the sum of absolute adjacency
eigenvalues, not a sum of squares; the defect is computed over the reals. -/
@[category research open, AMS 5 15 90]
theorem uniform_gap : ∃ ε : ℝ, 0 < ε ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsImperfect G → ε ≤ energy G / 2 - n + G.indepNum := by
  sorry

end Gebendorfer.EnergyIndependence
