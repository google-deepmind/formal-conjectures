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
# Pebbling number conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Graph_pebbling)
-/
variable {V : Type} {G : SimpleGraph V} [DecidableEq V]

/--
A Pebble distribution is an assigment of zero or more pebbles to each of the vertices.
-/
def PebbleDistribution (V : Type) := V → ℕ

/--
The number of pebbles of a distribution is the total number summed over all vertices.
-/
def NumberOfPebbles [Fintype V] : (PebbleDistribution V) → ℕ := fun D => ∑ v, D v

/--
A pebbling move on a graph consists of choosing a vertex with at least two pebbles, removing
two pebbles from it, and adding one to an adjacent vertex (the second removed pebble is discarded
from play).
-/
def IsPebblingMove (G : SimpleGraph V) (A B : PebbleDistribution V) : Prop :=
    ∃ v w : V, (A v) ≥ 2 ∧ G.Adj v w ∧
    B = (fun u =>
      if u = w then A u + 1
      else if u = v then A u - 2
      else A u)

@[category API, AMS 5]
theorem IsPebblingMove.refl (G : SimpleGraph V) (A : PebbleDistribution V) {v w : V} (hv : 2 ≤ A v)
    (hvw : G.Adj v w) :
    IsPebblingMove G A fun u =>
      if u = w then A u + 1
      else if u = v then A u - 2
      else A u :=
  ⟨v, w, hv, hvw, rfl⟩

/--
A pebble path is a series of pebbling moves.
-/
inductive PebblePath {α : Type} (r : α → α → Prop) : α → α → Type
  | refl (a : α) : PebblePath r a a
  | step {a b c : α} (p : PebblePath r a b) (h : r b c) : PebblePath r a c

/--
Indicates whether there exists a sequence of pebbling moves transforming one pebble distribution
to another.
-/
def ExistsPebblePath {α : Type} (r : α → α → Prop) (a b : α) : Prop :=
  Nonempty (PebblePath r a b)

/--
A pebble distribution `B` is reachable from another pebble distribution `A`, if there exists a
sequence of pebbling moves transforming the first into the second.
-/
def IsReachable (G : SimpleGraph V) (A B : PebbleDistribution V) : Prop :=
  ExistsPebblePath (IsPebblingMove G) A B

@[simp, category API, AMS 5]
theorem IsReachable.refl (G : SimpleGraph V) (A : PebbleDistribution V) : IsReachable G A A := by
  tauto

/--
The pebbling number of a graph `G`, is the lowest natural number `n` that satisfies the
following condition: Given any target or 'root' vertex in the graph and any initial
pebbles distribution with `n` pebbles on the graph, another pebble distribution is reachable
in which the designated root vertex has one or more pebbles.
-/
noncomputable def PebblingNumber [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf { n | ∀ D, NumberOfPebbles D = n → ∀ v, ∃ D', IsReachable G D D' ∧ 1 ≤ D' v }

/--
The pebbling number of the complete graph on `n` vertices is `n`.
-/
@[category API, AMS 5]
theorem PebblingNumber_completeGraph [Fintype V] :
    PebblingNumber (completeGraph V) = Fintype.card V := by
  refine IsLeast.csInf_eq ⟨fun D hD v => ?_, fun a ha => not_lt.1 fun ha_lt => ?_⟩
  · by_cases h : ∃ w, 2 ≤ D w
    · obtain ⟨w, hw⟩ := h
      by_cases hwv : w = v
      · exact ⟨D, .refl _ _, hwv ▸ Nat.one_le_of_lt hw⟩
      · exact ⟨fun u => if u = v then D u + 1 else if u = w then D u - 2 else D u,
          ⟨.step (.refl _) (.refl _ _ hw (by simpa))⟩, by simp⟩
    · refine ⟨D, by tauto, not_lt.1 fun hD' => ?_⟩
      exact Finset.sum_lt_sum (fun a s => Nat.le_of_lt_succ <| not_le.1 (h ⟨a, · ⟩))
        ⟨_, Finset.mem_univ _, hD'⟩ |>.trans_eq Fintype.card_eq_sum_ones.symm |>.ne hD
  · let R := Finset.equivFinOfCardEq (Finset.card_univ (α := V))
    let D : PebbleDistribution V := fun x ↦ if R ⟨_, Finset.mem_univ x⟩ < a then 1 else 0
    have hD : NumberOfPebbles D = a :=
      (Finset.sum_attach _ _).symm.trans ((R.sum_comp (if · < a then 1 else 0)).trans
        (.trans ( Finset.sum_fin_eq_sum_range _)
          (by norm_num [← Finset.mem_range, Finset.inter_eq_right.2, ha_lt.le])))
    obtain ⟨D', ⟨P⟩, h⟩ := ha D hD (R.symm ⟨a, ha_lt⟩)
    cases P with
    | refl => aesop
    | step p h =>
      obtain ⟨v, _, h, _, _⟩ := h
      exact absurd h (p.rec (by aesop) (by simp_all only [IsReachable, IsPebblingMove]; aesop) v)

/--
The pebbling number conjecture:
the pebbling number of a Cartesian product of graphs is at most equal to the product of the
pebbling numbers of the factors.
-/
@[category research open, AMS 5]
theorem pebbling_number_conjecture [Fintype V] (G H : SimpleGraph V) :
    PebblingNumber (G □ H) ≤ PebblingNumber G * PebblingNumber H := by
  sorry
