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
# Written on the Wall II - Conjecture 65

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture65

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 65](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/):

For a simple connected graph $G$, the size $f(G)$ of a largest induced forest satisfies
$f(G) \ge \operatorname{dist\_min}(A) + \lceil \operatorname{dist\_min}(M) / 3 \rceil$,
where $A$ is the set of minimum-degree vertices, $M$ is the set of maximum-degree vertices,
and $\operatorname{dist\_min}(S)$ is the minimum distance between two distinct vertices of $S$
(see `distMin`).
-/
@[category research open, AMS 5]
theorem conjecture65 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let A : Set α := {v | G.degree v = G.minDegree}
    let M : Set α := {v | G.degree v = G.maxDegree}
    (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedForestSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedForestSize := Nat.zero_le _

/-- In the complete graph `K₃`, min degree equals max degree (regular graph). -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 3)).minDegree = (⊤ : SimpleGraph (Fin 3)).maxDegree := by
  decide +native

/-- `distMin G S` is always nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (S : Set (Fin 3)) : 0 ≤ distMin G S := Nat.zero_le _

/-- In $K_2$, the minimum distance between its two vertices is $1$. -/
@[category test, AMS 5]
example : distMin (⊤ : SimpleGraph (Fin 2)) ({0, 1} : Set (Fin 2)) = 1 := by
  unfold distMin
  dsimp only
  split_ifs with h
  · rw [Finset.min'_eq_iff]
    constructor
    · refine Finset.mem_image.mpr ⟨(0, 1), ?_, ?_⟩
      · simp
      · simp
    · intro d hd
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      simp [SimpleGraph.dist_top_of_ne hne]
  · exfalso
    apply h
    exact ⟨(0, 1), by simp⟩

/-- A singleton contains no distinct pair, so `distMin` uses its degenerate-case fallback. -/
@[category test, AMS 5]
example : distMin (⊤ : SimpleGraph (Fin 3)) ({0} : Set (Fin 3)) = 0 := by
  simp [distMin]

end WrittenOnTheWallII.GraphConjecture65
