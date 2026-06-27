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
# Erdős Problem 150

*References:*
- [erdosproblems.com/150](https://www.erdosproblems.com/150)
- [Br24] Bradač, D., *On a question of Erdős and Nesetril about minimal cuts in a graph*.
  arXiv:2409.02974 (2024).
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. (1988), 81-92.
- [FKTV08] Fomin, Fedor V. and Kratsch, Dieter and Todinca, Ioan and Villanger, Yngve,
  *Exact algorithms for treewidth and minimum fill-in*. SIAM J. Comput. (2008), 1058--1079.
- [FoVi12] Fomin, Fedor V. and Villanger, Yngve, *Treewidth computation and extremal
  combinatorics*. Combinatorica (2012), 289--308.
- [GaMa18] Gaspers, Serge and Mackenzie, Simon, *On the number of minimal separators in graphs*.
  J. Graph Theory (2018), 653--659.
-/

namespace Erdos150

open Filter

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex set separating two vertices of a graph. -/
def IsSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  u ∉ T ∧ v ∉ T ∧ ∀ w : G.Walk u v, ∃ x ∈ w.support, x ∈ T

/-- An inclusion-minimal vertex separator between two vertices. -/
def IsMinSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  IsSeparator G u v T ∧ ∀ T' : Finset V, T' ⊂ T → ¬ IsSeparator G u v T'

/-- A minimal vertex cut is a minimal separator for some pair of distinct vertices. -/
def IsMinCut (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ IsMinSeparator G u v T

/-- The set of all minimal vertex cuts in a graph. -/
def minCutSet (G : SimpleGraph V) : Set (Finset V) :=
  {T | IsMinCut G T}

/-- The number of minimal vertex cuts in a graph. -/
noncomputable def numMinCuts (G : SimpleGraph V) : ℕ :=
  (minCutSet G).ncard

/-- The maximum possible number of minimal cuts in a graph on $n$ vertices. -/
noncomputable def c (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), numMinCuts G = k}

/--
A minimal cut of a graph is a minimal set of vertices whose removal disconnects the graph. Let $c(n)$ be the maximum number of minimal cuts a graph on $n$ vertices can have.

Does $c(n)^{1/n}\to \alpha$ for some $\alpha <2$?

Bradač [Br24] proved that the limit exists, and Fomin--Villanger bounds give $\alpha < 2$.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos150.lean"]
theorem erdos_150 :
    ∃ α : ℝ, Tendsto (fun n : ℕ => (c n : ℝ) ^ (1 / (n : ℝ))) atTop (nhds α) ∧
      α < 2 := by
  sorry

end Erdos150
