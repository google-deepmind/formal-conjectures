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
# Written on the Wall II — Conjecture 91

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 91, 10 April 2004](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, The Bipartite–Forest Gap Is Unbounded in Claw-Free Graphs, 25 July 2026; written line-graph family and intake](https://github.com/user-attachments/files/33372239/Gebendorfer_WOWII_91_Intake_2026-10-13.zip)

The catalogue already records another refutation, obtained by bridging $K_{3,3}$
to $K_8$. The cited line-graph family is not asserted to be the first refutation.
The archived O status is not a current worldwide-openness claim.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture91
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bipartiteNumber (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset V, A.card = k ∧ (G.induce (A : Set V)).IsBipartite}

noncomputable def forestNumber (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset V, A.card = k ∧ (G.induce (A : Set V)).IsAcyclic}

/-- The average independence number of the graphs induced by open neighborhoods. -/
noncomputable def averageLocalIndependence (G : SimpleGraph V) : ℚ := by
  classical
  exact (∑ v : V, ((G.induce (G.neighborSet v)).indepNum : ℚ)) / Fintype.card V

/-! A finite graph witness: the line graph of three four-cycles
joined by two bridges. The ordered endpoints encode the fourteen
edges of the underlying twelve-vertex graph. -/
def witnessEndpoints (i : Fin 14) : Fin 12 × Fin 12 :=
  if i = 0 then (0, 1)
  else if i = 1 then (1, 2)
  else if i = 2 then (2, 3)
  else if i = 3 then (3, 0)
  else if i = 4 then (4, 5)
  else if i = 5 then (5, 6)
  else if i = 6 then (6, 7)
  else if i = 7 then (7, 4)
  else if i = 8 then (8, 9)
  else if i = 9 then (9, 10)
  else if i = 10 then (10, 11)
  else if i = 11 then (11, 8)
  else if i = 12 then (0, 4)
  else (4, 8)

def witnessGraph : SimpleGraph (Fin 14) where
  Adj i j := i ≠ j ∧
    ((witnessEndpoints i).1 = (witnessEndpoints j).1 ∨
     (witnessEndpoints i).1 = (witnessEndpoints j).2 ∨
     (witnessEndpoints i).2 = (witnessEndpoints j).1 ∨
     (witnessEndpoints i).2 = (witnessEndpoints j).2)
  symm := ⟨by
    intro i j h
    rcases h with ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inr h.symm))⟩
  loopless := ⟨by
    intro i h
    exact h.1 rfl⟩

/-- The exact rational contradiction required after proving the
finite witness's graph invariants. -/
@[category test, AMS 5]
theorem witness_numeric_contradiction :
    ¬ ((12 : ℚ) ≤ 1 + (10 : ℚ) * 2 / 2) := by
  norm_num

/-- It is false that every connected finite simple graph satisfies
$b(G)\le1+f(G)\lceil\operatorname{avg}_v\alpha(G[N(v)])\rceil/2$.
Both induced-subgraph invariants maximize their vertex orders; the factor one
half is retained as rational division after the ceiling of the average. -/
@[category research solved, AMS 5]
theorem conjecture91 : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected →
    (bipartiteNumber G : ℚ) ≤ 1 + (forestNumber G : ℚ) *
      (⌈averageLocalIndependence G⌉₊ : ℚ) / 2 := by
  sorry

end WrittenOnTheWallII.GraphConjecture91
