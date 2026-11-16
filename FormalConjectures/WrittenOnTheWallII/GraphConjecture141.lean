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
module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 141

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture141

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 141](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\mathrm{tree}(G) \ge (1/2) \cdot \mathrm{girth}(G) - 1 + \max_v l(v)$
where $\mathrm{tree}(G)$ is the number of vertices of a largest induced tree subgraph,
$\mathrm{girth}(G)$ is the length of the shortest cycle ($0$ if acyclic), and
$l(v)$ (`indepNeighborsCard G v`) is the independence number of the neighbourhood of $v$.
-/
@[category research solved, AMS 5]
theorem conjecture141 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (G.girth : ℝ) / 2 - 1 + ((Finset.univ.sup (indepNeighborsCard G) : ℕ) : ℝ) ≤
    (largestInducedTreeSize G : ℝ) := by
  classical
  obtain ⟨v, -, hv⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset α) Finset.univ_nonempty
      (indepNeighborsCard G)
  have hstar : Finset.univ.sup (indepNeighborsCard G) + 1 ≤ largestInducedTreeSize G := by
    rw [hv]
    exact indepNeighborsCard_add_one_le_largestInducedTreeSize G v
  have key : G.girth + 2 * Finset.univ.sup (indepNeighborsCard G) ≤
      2 * largestInducedTreeSize G + 2 := by
    by_cases hcyc : G.IsAcyclic
    · rw [hcyc.girth_eq_zero]
      omega
    · have hg3 : 3 ≤ G.girth := G.three_le_girth hcyc
      rcases Nat.lt_or_ge G.girth 4 with hg3' | hg4
      · omega
      · have hmain := maxDegree_add_girth_le_largestInducedTreeSize_add_three G h hcyc hg4
        have hsup : Finset.univ.sup (indepNeighborsCard G) ≤ G.maxDegree :=
          Finset.sup_le fun w _ =>
            (indepNeighborsCard_le_degree G w).trans (G.degree_le_maxDegree w)
        omega
  have := (Nat.cast_le (α := ℝ)).2 key
  push_cast at this
  linarith

-- Sanity checks

/-- The `largestInducedTreeSize` invariant is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The path graph `P₃` has 3 vertices; `n P₃ = 3`. -/
@[category test, AMS 5]
example : Fintype.card (Fin 3) = 3 := by decide

end WrittenOnTheWallII.GraphConjecture141
