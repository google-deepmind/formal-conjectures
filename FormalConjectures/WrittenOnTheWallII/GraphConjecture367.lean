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
# Written on the Wall II - Conjecture 367

The proposed lower bound relates the total domination number of a tree to the number
of distinct degrees when degree two is most frequent. We distinguish unique modes
from modes that may tie with other degrees.

*References:*
- [E. DeLaVina, Written on the Wall II](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [DeLaVina, Larson, Pepper and Waller, Conjecture 6, p. 12](https://math1um.github.io/Research/r05.pdf)
- [J. J. Gebendorfer, A quadratic degree-diversity bound for trees]
  (https://github.com/RhudeJJJJ/formal-conjectures/blob/d8348148865175409dc83ac241ce342f43d395c3/Papers/20261021/wowii367.tex)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture367

open SimpleGraph

/-- Number of vertices of ambient degree $j$. -/
def degreeCount {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) : ℕ :=
  (Finset.univ.filter fun v => G.degree v = j).card

/-- Number of distinct ambient degrees. -/
def distinctDegreeCount {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (fun v => G.degree v)).card

/-- Degree two is a mode, allowing a tie with any other degree. -/
def TwoIsMode {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, degreeCount G (G.degree v) ≤ degreeCount G 2

/-- Degree two is the unique mode. -/
def TwoIsUniqueMode {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  0 < degreeCount G 2 ∧
    ∀ v, G.degree v ≠ 2 → degreeCount G (G.degree v) < degreeCount G 2

/-- The reading that permits tied modes. Multiplication clears the denominator. -/
def tiedModeStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V → TwoIsMode G →
      4 * distinctDegreeCount G ≤ 3 * G.totalDominationNumber

private instance pathFourDecidable : DecidableRel (pathGraph 4).Adj :=
  fun u v => decidable_of_iff (u.val + 1 = v.val ∨ v.val + 1 = u.val)
    pathGraph_adj.symm

@[category test, AMS 5]
private theorem path_four_tree : (pathGraph 4).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected 3, ?_⟩
  have he : (pathGraph 4).edgeFinset.card = 3 := by decide +kernel
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, he,
    Nat.card_eq_fintype_card]
  decide

@[category test, AMS 5]
private theorem path_four_total_upper : (pathGraph 4).totalDominationNumber ≤ 2 := by
  apply csInf_le (OrderBot.bddBelow _)
  refine ⟨({1, 2} : Finset (Fin 4)), ?_⟩
  constructor
  · change ∀ v : Fin 4, ∃ w ∈ ({1, 2} : Finset (Fin 4)), (pathGraph 4).Adj v w
    decide
  · decide

/-- The tied-mode reading is false: the four-vertex path has two degree-one
vertices, two degree-two vertices, and a total dominating set of size two. -/
@[category research solved, question, AMS 5]
theorem not_tied_mode_statement : ¬ tiedModeStatement := by
  intro h
  have hm : TwoIsMode (pathGraph 4) := by
    change ∀ v : Fin 4, degreeCount (pathGraph 4) ((pathGraph 4).degree v) ≤
      degreeCount (pathGraph 4) 2
    decide +kernel
  have hd : distinctDegreeCount (pathGraph 4) = 2 := by decide +kernel
  have hb := h (Fin 4) (pathGraph 4) path_four_tree (by decide +kernel) hm
  rw [hd] at hb
  have hu := path_four_total_upper
  omega

/--
The unique-mode interpretation of WOWII 367: a tree on more than two vertices whose
unique most frequent degree is two has $3\gamma_t(T)\geq4\operatorname{dd}(T)$.
The source does not specify whether ties are admitted.
-/
@[category research open, question, AMS 5]
theorem unique_mode :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V → TwoIsUniqueMode G →
        4 * distinctDegreeCount G ≤ 3 * G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture367
