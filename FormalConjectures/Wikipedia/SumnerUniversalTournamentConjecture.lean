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
# Sumner's universal tournament conjecture (1971)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Sumner%27s_conjecture)
* [HT91] Häggkvist, R. and Thomason, A. (1991). "Trees in tournaments." *Combinatorica* 11,
  pp. 123--130.
* [ES04] El Sahili, A. (2004). "Trees in tournaments." *J. Combin. Theory Ser. B* 92,
  pp. 183--187.
* [KMO11] Kühn, D., Mycroft, R. and Osthus, D. (2011). "A proof of Sumner's universal
  tournament conjecture for large tournaments." *Proc. London Math. Soc.* 102, pp. 731--766.
  [arXiv:1010.4430](https://arxiv.org/abs/1010.4430)
-/

@[expose] public section

open SimpleGraph Digraph

namespace SumnerUniversalTournamentConjecture

/-- An **oriented tree**: a digraph that is an orientation of a tree. -/
def IsOrientedTree {W : Type*} (D : Digraph W) : Prop :=
  ∃ T : SimpleGraph W, T.IsTree ∧ D.IsOrientation T

/-- The digraph `D` **embeds** in `D'`: there is an injective digraph homomorphism `D →g D'`. -/
def Embeds {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (D : Digraph W) (D' : Digraph V) : Prop :=
  ∃ f : D →g D', Function.Injective f

/--
**Sumner's universal tournament conjecture (1971).**

Every tournament on $2n - 2$ vertices contains every oriented tree on $n \ge 2$ vertices as a
subgraph.
-/
@[category research open, AMS 5]
theorem sumner_conjecture :
    ∀ (n : ℕ), 2 ≤ n →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
        Fintype.card W = n → IsOrientedTree D →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
          Fintype.card V = 2 * n - 2 → G.IsTournament → Embeds D G := by
  sorry

/--
**Kühn–Mycroft–Osthus (2011): the conjecture holds for all sufficiently large $n$.**

*Reference:* [KMO11].
-/
@[category research solved, AMS 5]
theorem sumner_conjecture.variants.large_n :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
        Fintype.card W = n → IsOrientedTree D →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
          Fintype.card V = 2 * n - 2 → G.IsTournament → Embeds D G := by
  sorry

/--
**El Sahili (2004): tournaments on $3n - 3$ vertices suffice.**

Every tournament on $3n - 3$ vertices contains every oriented tree on $n \ge 2$ vertices,
improving the bound $12n$ of Häggkvist and Thomason [HT91].

*Reference:* [ES04].
-/
@[category research solved, AMS 5]
theorem sumner_conjecture.variants.el_sahili (n : ℕ) (hn : 2 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hD : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 3 * n - 3) (hG : G.IsTournament) : Embeds D G := by
  sorry

/-- The rotational tournament on `Fin (2n - 3)`: `i → j` when `j - i ∈ {1, …, n - 2}`
modulo `2n - 3`. -/
private def sharpRot (n : ℕ) : Digraph (Fin (2 * n - 3)) where
  Adj i j :=
    (i.val < j.val ∧ j.val ≤ i.val + (n - 2)) ∨ (j.val < i.val ∧ j.val + (n - 1) ≤ i.val)

/-- The out-star with centre `c`: arcs from `c` to every other vertex. -/
private def sharpOutStar {W : Type} (c : W) : Digraph W where
  Adj u v := u = c ∧ v ≠ c

@[category API, AMS 5]
private theorem sharpRot_isTournament (n : ℕ) : (sharpRot n).IsTournament := by
  refine ⟨fun v h => ?_, fun u v huv => ?_⟩
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have h : u.val ≠ v.val := fun h => huv (Fin.ext h)
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) (⟨h3, h4⟩ | ⟨h3, h4⟩) <;> omega
  intro hn
  rcases lt_or_gt_of_ne h with hlt | hgt
  · by_cases h2 : v.val ≤ u.val + (n - 2)
    · exact Or.inl ⟨hlt, h2⟩
    · exact absurd (show (sharpRot n).Adj v u from Or.inr ⟨hlt, by omega⟩) hn
  · by_cases h2 : v.val + (n - 1) ≤ u.val
    · exact Or.inr ⟨hgt, h2⟩
    · exact absurd (show (sharpRot n).Adj v u from Or.inl ⟨hgt, by omega⟩) hn

@[category API, AMS 5]
private theorem sharpOutStar_isOrientation {W : Type} (c : W) :
    (sharpOutStar c).IsOrientation (starGraph c) := by
  constructor
  · intro u v h
    obtain ⟨hu, hv⟩ := h
    rw [starGraph_adj]
    exact ⟨fun h => hv (h ▸ hu), Or.inl hu⟩
  · intro u v h
    rw [starGraph_adj] at h
    rcases h with ⟨hne, rfl | rfl⟩
    · exact ⟨fun _ h => h.2 rfl, fun _ => ⟨rfl, Ne.symm hne⟩⟩
    · exact ⟨fun h => (h.2 rfl).elim, fun h => (h ⟨rfl, hne⟩).elim⟩

/-- The sharpCode of `y` relative to `x`: `(y - x - 1) mod (2n - 3)`. -/
private def sharpCode (n : ℕ) (x y : Fin (2 * n - 3)) : ℕ :=
  if x.val < y.val then y.val - x.val - 1 else y.val + (2 * n - 3) - x.val - 1

@[category API, AMS 5]
private theorem sharpCode_lt {n : ℕ} {x y : Fin (2 * n - 3)} (h : (sharpRot n).Adj x y) :
    sharpCode n x y < n - 2 := by
  have hx := x.isLt
  have hy := y.isLt
  unfold sharpCode
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> split_ifs <;> omega

@[category API, AMS 5]
private theorem sharpCode_inj {n : ℕ} {x y z : Fin (2 * n - 3)} (hy : (sharpRot n).Adj x y)
    (hz : (sharpRot n).Adj x z)
    (h : sharpCode n x y = sharpCode n x z) : y = z := by
  have hx' := x.isLt
  have hy' := y.isLt
  have hz' := z.isLt
  unfold sharpCode at h
  apply Fin.ext
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hz with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    split_ifs at h <;> omega

/-- The leaves `1, …, n - 1` of the out-star on `Fin n`. -/
private def sharpLeaf (n : ℕ) (k : Fin (n - 1)) : Fin n :=
  ⟨k.val + 1, by have := k.isLt; omega⟩

/--
**The bound $2n - 2$ would be sharp.**

For every $n \ge 2$ there is an oriented tree on $n$ vertices — the out-star, with arcs from a
centre to the $n - 1$ other vertices — that embeds in no regular tournament on $2n - 3$ vertices:
every vertex of such a tournament has out-degree $n - 2 < n - 1$.
-/
@[category research solved, AMS 5]
theorem sumner_conjecture.variants.sharp (n : ℕ) (hn : 2 ≤ n) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G := by
  obtain ⟨c, hc⟩ : ∃ c : Fin n, c.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  refine ⟨Fin n, inferInstance, inferInstance, sharpOutStar c, Classical.decRel _,
    Fintype.card_fin n, ⟨starGraph c, isTree_starGraph c, sharpOutStar_isOrientation c⟩,
    Fin (2 * n - 3), inferInstance, inferInstance, sharpRot n, Classical.decRel _,
    Fintype.card_fin _, sharpRot_isTournament n, ?_⟩
  rintro ⟨f, hf⟩
  have hleaf : ∀ k, sharpLeaf n k ≠ c := fun k h =>
    Nat.succ_ne_zero k.val ((congrArg Fin.val h).trans hc)
  have hadj : ∀ k, (sharpRot n).Adj (f c) (f (sharpLeaf n k)) := fun k =>
    f.map_adj' ⟨rfl, hleaf k⟩
  have hg := Fintype.card_le_of_injective
    (fun k : Fin (n - 1) =>
      (⟨sharpCode n (f c) (f (sharpLeaf n k)), sharpCode_lt (hadj k)⟩ : Fin (n - 2)))
    (by
      intro k₁ k₂ h
      have h' := hf (sharpCode_inj (hadj k₁) (hadj k₂) (congrArg Fin.val h))
      have h'' := congrArg Fin.val h'
      simp only [sharpLeaf] at h''
      exact Fin.ext (by omega))
  simp only [Fintype.card_fin] at hg
  omega

end SumnerUniversalTournamentConjecture
