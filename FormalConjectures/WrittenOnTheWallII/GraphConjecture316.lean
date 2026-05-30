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

import FormalConjectures.Util.ProblemImports
/-!
# Written on the Wall II - Conjecture 316

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture316

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The path `0-1-2-3-4` on five vertices, `P₅`, as an explicit `SimpleGraph (Fin 5)`. -/
def P5 : SimpleGraph (Fin 5) where
  Adj a b := a.val + 1 = b.val ∨ b.val + 1 = a.val
  symm := fun _ _ h => h.symm
  loopless := fun _ h => by rcases h with h | h <;> omega

instance : DecidableRel P5.Adj := fun a b =>
  inferInstanceAs (Decidable (a.val + 1 = b.val ∨ b.val + 1 = a.val))

private lemma P5_connected : P5.Connected := by decide

private lemma P5_hyp : (averageDegree P5 : ℚ) ≤ (pendantVertices P5).card := by
  have hp : (pendantVertices P5).card = 2 := by decide
  have hd : (∑ v : Fin 5, P5.degree v) = 8 := by decide
  unfold averageDegree
  rw [← Nat.cast_sum, hd, hp]
  norm_num [Fintype.card_fin]

/-- `{1, 2, 3}` is a minimal total dominating set of `P₅` (of size 3). -/
private lemma P5_min_3 : IsMinimalTotalDominatingSet P5 {1, 2, 3} := by
  unfold IsMinimalTotalDominatingSet IsTotalDominatingSet; decide

/-- `{0, 1, 3, 4}` is a minimal total dominating set of `P₅` (of size 4): every total
dominating set must contain `1` and `3` to dominate the leaves `0` and `4`. -/
private lemma P5_min_4 : IsMinimalTotalDominatingSet P5 {0, 1, 3, 4} := by
  unfold IsMinimalTotalDominatingSet IsTotalDominatingSet; decide

/-- `P₅` has minimal total dominating sets of sizes 3 and 4, so it is not WTD. -/
private lemma P5_not_wtd : ¬ IsWellTotallyDominated P5 := fun h => by
  have e : ({1, 2, 3} : Finset (Fin 5)).card = ({0, 1, 3, 4} : Finset (Fin 5)).card :=
    h _ _ P5_min_3 P5_min_4
  revert e; decide

/--
WOWII [Conjecture 316](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

Let `G` be a simple connected graph and let `P` denote the set of pendant vertices
(vertices of degree 1). If `|P| ≥ deg_avg(G)`, then `G` is well totally dominated,
where `deg_avg(G)` is the average degree of `G`.

This is **false**. The path on five vertices `P₅` is a counterexample: it is connected with
`deg_avg(P₅) = 8/5 ≤ 2 = |P|`, yet it is not well totally dominated, since `{1, 2, 3}` and
`{0, 1, 3, 4}` are both minimal total dominating sets, of sizes 3 and 4 respectively. (That a
path on five vertices is not WTD is also recorded in Bahadır–Ekim–Gözüpek, *Well-Totally-
Dominated Graphs*, arXiv:2010.02341; the same `P₅` already disproves WOWII Conjecture 32 in
this repository.)
-/
@[category research solved, AMS 5]
theorem conjecture316 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj],
      G.Connected → (averageDegree G : ℚ) ≤ (pendantVertices G).card →
      IsWellTotallyDominated G :=
  ⟨False.elim, fun h => P5_not_wtd (h (Fin 5) P5 P5_connected P5_hyp)⟩

-- Sanity checks

/-- The average degree of the edgeless graph on 3 vertices is 0. -/
@[category test, AMS 5]
example : averageDegree (⊥ : SimpleGraph (Fin 3)) = 0 := by
  unfold averageDegree; simp [Fintype.card_fin]

/-- In `P₃` (path 0-1-2), the average degree is 4/3 and there are 2 pendant vertices. -/
@[category test, AMS 5]
example : averageDegree (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) = 4/3 := by
  unfold averageDegree; decide +native

end WrittenOnTheWallII.GraphConjecture316
