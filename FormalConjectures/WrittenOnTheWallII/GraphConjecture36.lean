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
# Written on the Wall II - Conjecture 36

The conjecture is false. The counterexample below has a subdivided triangle on
vertices `0`, `1`, `9`; vertices `7`, `8` adjacent to all three triangle
vertices; and leaves `3`, `2` attached to `7`, `8`, respectively. It has radius
three, one diametrical pair, and largest induced-path order five.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture36

open Classical SimpleGraph

/-- `dp G` is the number of diametrical pairs of `G`: the number of unordered
pairs `{u, v}` of vertices at distance `diam(G)`.  -/
noncomputable def dp {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  (Finset.univ.filter
    (fun p : Sym2 α => p.lift ⟨fun u v => G.dist u v = G.diam ∧ u ≠ v,
      fun u v => by simp [SimpleGraph.dist_comm, ne_comm]⟩)).card

/-- A 10-vertex counterexample to Conjecture 36. -/
abbrev wowii36Counterexample : SimpleGraph (Fin 10) :=
  SimpleGraph.fromEdgeSet {
    s(0, 4), s(0, 5), s(0, 7), s(0, 8),
    s(1, 4), s(1, 6), s(1, 7), s(1, 8),
    s(2, 8), s(3, 7),
    s(5, 9), s(6, 9), s(7, 9), s(8, 9)
  }

/-- The counterexample is connected. -/
@[category test, AMS 5]
theorem wowii36Counterexample_connected : wowii36Counterexample.Connected := by
  decide +native

/-- The counterexample has radius three. -/
@[category test, AMS 5]
theorem wowii36Counterexample_radius : wowii36Counterexample.radius.toNat = 3 := by
  rw [radius_eq_computable wowii36Counterexample wowii36Counterexample_connected]
  decide +native

/-- The counterexample contains no induced path on six vertices. -/
@[category test, AMS 5]
theorem wowii36Counterexample_no_inducedPath6 :
    ¬ ∃ e : Fin 6 → Fin 10, Function.Injective e ∧
      ∀ i j : Fin 6, wowii36Counterexample.Adj (e i) (e j) ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  native_decide

/-- The largest induced path in the counterexample has exactly five vertices. -/
@[category test, AMS 5]
theorem wowii36Counterexample_path : path wowii36Counterexample = 5 := by
  apply Nat.le_antisymm
  · exact path_le_of_not_exists_inducedPath_succ wowii36Counterexample 5
      wowii36Counterexample_no_inducedPath6
  · have hpath : wowii36Counterexample.isInducedPath [2, 8, 0, 7, 3] := by
      constructor
      · decide
      · intro i j
        fin_cases i <;> fin_cases j <;> native_decide
    simpa using length_le_path_of_isInducedPath
      wowii36Counterexample [2, 8, 0, 7, 3] hpath

/-- The counterexample has a unique diametrical pair, namely `{2, 3}`. -/
@[category test, AMS 5]
theorem wowii36Counterexample_dp : dp wowii36Counterexample = 1 := by
  have hdiam : wowii36Counterexample.diam = 4 := by
    unfold SimpleGraph.diam
    rw [ediam_eq_computable wowii36Counterexample wowii36Counterexample_connected]
    decide +native
  unfold dp
  rw [Finset.card_eq_one]
  refine ⟨s(2, 3), ?_⟩
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  induction pair using Sym2.inductionOn with
  | _ u v =>
      simp only [Sym2.lift_mk]
      rw [hdiam, SimpleGraph.dist_eq_computable]
      fin_cases u <;> fin_cases v <;> native_decide

/--
WOWII [Conjecture 36](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj36):

For every finite simple connected graph $G$,
$\operatorname{path}(G) \ge 2 \cdot \operatorname{rad}(G) / \operatorname{dp}(G)$,
where $\operatorname{path}(G)$ is the number of vertices in a largest induced path,
$\operatorname{rad}(G)$ is the radius of $G$, and $\operatorname{dp}(G)$ is the number
of *diametrical pairs* of $G$ — that is, the number of pairs of vertices at distance
$\operatorname{diam}(G)$.

Disproved by Waller in Oct 2003 (counterexample: path number 5, radius 3, dp 1).
-/
@[category research solved, AMS 5]
theorem conjecture36 : answer(False) ↔
    ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α],
      ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_ : G.Connected) (_ : 0 < dp G),
        (2 * G.radius.toNat : ℝ) / (dp G : ℝ) ≤ (path G : ℝ) := by
  show False ↔ _
  rw [false_iff]
  intro h
  have hbad := h (α := Fin 10) wowii36Counterexample
    wowii36Counterexample_connected (by
      rw [wowii36Counterexample_dp]
      norm_num)
  rw [wowii36Counterexample_radius, wowii36Counterexample_dp,
    wowii36Counterexample_path] at hbad
  norm_num at hbad

-- Sanity checks

/-- The `path G` invariant is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℝ) := Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture36
