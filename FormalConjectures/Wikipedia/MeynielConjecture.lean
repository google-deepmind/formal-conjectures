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
# Meyniel's conjecture on the cop number

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Cop_number)
* [Fr87] Frankl, P. (1987). "Cops and robbers in graphs with large girth and Cayley graphs."
  *Discrete Appl. Math.* 17, pp. 301--305.
* [NW83] Nowakowski, R. and Winkler, P. (1983). "Vertex-to-vertex pursuit in a graph."
  *Discrete Math.* 43, pp. 235--239.
* [SS11] Scott, A. and Sudakov, B. (2011). "A bound for the cops and robbers problem."
  *SIAM J. Discrete Math.* 25, pp. 1438--1442.
* [BB12] Baird, W. and Bonato, A. (2012). "Meyniel's conjecture on the cop number: a survey."
  *J. Comb.* 3, pp. 225--238.
-/

open Filter

namespace MeynielConjecture

variable {V : Type*}

/-- A **move** in the cops-and-robbers game: stay put, or slide along an edge. -/
def Step (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v

/-- `CopsCatchWithin G k m c r`: with `k` cops at positions `c`, the robber at `r`, and the cops
to move, the cops can guarantee to catch the robber within `m` further rounds. In each round
every cop moves (or stays), catching the robber if a cop reaches the robber's vertex, and then
the robber moves (or stays). -/
def CopsCatchWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | m + 1, c, r =>
      (∃ i, c i = r) ∨
        ∃ c' : Fin k → V, (∀ i, Step G (c i) (c' i)) ∧
          ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CopsCatchWithin G k m c' r')

/-- `k` cops have a winning strategy on `G`: they can choose starting positions such that,
wherever the robber starts, they catch the robber in finitely many rounds. -/
def CopsWin (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ m, CopsCatchWithin G k m c r

/-- The **cop number** `c(G)`: the least number of cops that can guarantee to catch the
robber on `G`. -/
noncomputable def copNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | CopsWin G k}

/-- Zero cops never catch a robber. -/
@[category API, AMS 5 91]
lemma not_copsCatchWithin_zero (G : SimpleGraph V) (m : ℕ) (c : Fin 0 → V) (r : V) :
    ¬CopsCatchWithin G 0 m c r := by
  induction m generalizing c r with
  | zero =>
    rintro ⟨i, -⟩
    exact i.elim0
  | succ m ih =>
    rintro (⟨i, -⟩ | ⟨c', -, ⟨i, -⟩ | h⟩)
    · exact i.elim0
    · exact i.elim0
    · exact ih c' r (h r (Or.inl rfl))

/-- On a graph with at least one vertex, zero cops do not win. -/
@[category API, AMS 5 91]
lemma not_copsWin_zero [Nonempty V] (G : SimpleGraph V) : ¬CopsWin G 0 := by
  rintro ⟨c, hc⟩
  obtain ⟨m, hm⟩ := hc (Classical.arbitrary V)
  exact not_copsCatchWithin_zero G m c _ hm

/-- One cop per vertex wins. -/
@[category API, AMS 5 91]
lemma copsWin_card [Fintype V] (G : SimpleGraph V) : CopsWin G (Fintype.card V) :=
  ⟨(Fintype.equivFin V).symm, fun r => ⟨0, ⟨Fintype.equivFin V r, by simp⟩⟩⟩

/-- On a graph with at least one vertex, at least one cop is needed. -/
@[category API, AMS 5 91]
lemma one_le_copNumber [Fintype V] [Nonempty V] (G : SimpleGraph V) : 1 ≤ copNumber G := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rcases Nat.sInf_eq_zero.mp h0 with h | h
  · exact not_copsWin_zero G h
  · exact Set.eq_empty_iff_forall_notMem.mp h _ (copsWin_card G)

/--
**Meyniel's conjecture (c. 1985).**

There is a universal constant `C` such that every connected graph on `n` vertices has cop
number at most `C √n`: a team of `O(√n)` cops can always catch the robber in the game of cops
and robbers. The conjecture was communicated by Meyniel to Frankl and first appeared in
[Fr87]; see [BB12] for a survey.
-/
@[category research open, AMS 5 91]
theorem meyniel_conjecture :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * Real.sqrt (Fintype.card V) := by
  sorry

/--
**The soft Meyniel conjecture.**

There are constants `ε, C > 0` such that every connected graph on `n` vertices has cop number
at most `C n^(1 - ε)`. Even this weakening of Meyniel's conjecture is open; no bound of the
form `O(n^(1 - ε))` is known. See [BB12].
-/
@[category research open, AMS 5 91]
theorem meyniel_conjecture.variants.soft :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      (copNumber G : ℝ) ≤ C * (Fintype.card V : ℝ) ^ ((1 : ℝ) - ε) := by
  sorry

/--
**Scott–Sudakov (2011): the best known general bound.**

Every connected graph on `n` vertices has cop number at most `n / 2^((1 - o(1)) √(log₂ n))`.
This (together with the same bound obtained independently by Lu–Peng and by Frieze, Krivelevich
and Loh) is the best known bound towards Meyniel's conjecture.

*Reference:* [SS11].
-/
@[category research solved, AMS 5 91]
theorem meyniel_conjecture.variants.scott_sudakov :
    ∃ f : ℕ → ℝ, Tendsto f atTop (nhds 0) ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
        (copNumber G : ℝ) ≤ (Fintype.card V : ℝ) /
          2 ^ ((1 - f (Fintype.card V)) * Real.sqrt (Real.logb 2 (Fintype.card V))) := by
  sorry

/--
**Trees are cop-win (Nowakowski–Winkler 1983).**

Every nonempty tree has cop number `1`: a single cop, always moving towards the robber, catches
the robber on any connected acyclic graph. More generally, the cop-win graphs are exactly the
dismantlable graphs.

*Reference:* [NW83].
-/
@[category research solved, AMS 5 91]
theorem meyniel_conjecture.variants.tree {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hc : G.Connected) (ha : G.IsAcyclic) :
    copNumber G = 1 := by
  sorry

/--
**Complete graphs have cop number `1`.**

A single cop starting anywhere catches the robber on a nonempty complete graph in one move.
-/
@[category test, AMS 5 91]
theorem meyniel_conjecture.variants.complete {V : Type} [Fintype V] [Nonempty V] :
    copNumber (⊤ : SimpleGraph V) = 1 := by
  refine le_antisymm (Nat.sInf_le ?_) (one_le_copNumber _)
  refine ⟨fun _ => Classical.arbitrary V, fun r => ?_⟩
  by_cases hr : Classical.arbitrary V = r
  · exact ⟨0, ⟨0, hr⟩⟩
  · refine ⟨1, Or.inr ⟨fun _ => r, fun i => Or.inr ?_, Or.inl ⟨0, rfl⟩⟩⟩
    exact hr

/--
**The number of vertices is enough cops.**

Placing one cop on every vertex catches the robber immediately, so `c(G) ≤ |V|`.
-/
@[category test, AMS 5 91]
theorem meyniel_conjecture.variants.copNumber_le_card [Fintype V] (G : SimpleGraph V) :
    copNumber G ≤ Fintype.card V :=
  Nat.sInf_le (copsWin_card G)

end MeynielConjecture
