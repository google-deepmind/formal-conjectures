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

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def IsDominatingSet (S : Finset V) : Prop := ∀ v ∉ S, ∃ u ∈ S, G.Adj v u

noncomputable def independentDominationNumber : ℕ :=
  ⨅ (S : Finset V) (_ : G.IsIndepSet S ∧ IsDominatingSet G S), S.card

variable (D := G.maxDegree) (i := independentDominationNumber G) (n := Fintype.card V)

theorem independentDominationEven (hIso : 0 < G.minDegree) (hMax : 1 ≤ D) (hEven : Even D) :
    (D + 2)^2 * i ≤ (D^2 + 4) * n := by
  sorry

theorem independentDominationOdd (hIso : 0 < G.minDegree) (hMax : 1 ≤ D) (hOdd : Odd D) :
    (D + 1) * (D + 3) * i ≤ (D^2 + 3) * n := by
  sorry
