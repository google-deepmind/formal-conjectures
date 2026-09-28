test line
second/-
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
# Erdős Problem 149

*References:*
- [erdosproblems.com/149](https://www.erdosproblems.com/149)
- [FGST89] Faudree, R. J., Gyárfás, A., Schelp, R. H. and Tuza, Zs., Induced matchings in
  bipartite graphs. Discrete Math. (1989), 83-87.
- [An92] Andersen, L. D., The strong chromatic index of a cubic graph is at most 10. Discrete
  Math. (1992), 231-252.
- [HHT93] Horák, P., He, Q. and Trotter, W. T., Induced matchings in cubic graphs. J. Graph
  Theory (1993), 151-160.
- [HJK22] Hurley, E., de Joannis de Verclos, R. and Kang, R. J., An improved procedure for
  colouring graphs of bounded local density. Adv. Comb. (2022).
-/

@[expose] public section

open Finset SimpleGraph

namespace Erdos149

/--
Let $G$ be a finite graph with maximum degree $\Delta$. Is it true that
$sq(G) \le \frac{5}{4}\Delta^2$?

Here $sq(G)$ is the strong chromatic index: the least $k$ such that the edges of $G$ can be
partitioned into $k$ sets of strongly independent edges. A question of Erdős and Nešetřil.
-/
@[category research open, AMS 5]
theorem erdos_149 :
    answer(sorry) ↔ ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (G.strongChromaticIndex : ℝ) ≤ 5 / 4 * (G.maxDegree : ℝ) ^ 2 := by
  sorry

/-- The trivial greedy bound $sq(G) \le 2\Delta^2 - 2\Delta + 1$. -/
@[category textbook, AMS 5]
theorem erdos_149.variants.trivial (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.strongChromaticIndex ≤ 2 * G.maxDegree ^ 2 - 2 * G.maxDegree + 1 :=
  G.strongChromaticIndex_le_two_mul_sq

/-- Hurley, de Joannis de Verclos and Kang [HJK22] proved $sq(G) \le 1.772\Delta^2$ for all
graphs with sufficiently large maximum degree $\Delta$. -/
@[category research solved, AMS 5]
theorem erdos_149.variants.hjk22 :
    ∃ D₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      D₀ ≤ G.maxDegree →
        (G.strongChromaticIndex : ℝ) ≤ 1.772 * (G.maxDegree : ℝ) ^ 2 := by
  sorry

/-- Andersen [An92] and Horák, He and Trotter [HHT93] proved $sq(G) \le 10$ when
$\Delta \le 3$. This agrees with the conjectured bound $\frac{5\Delta^2 - 2\Delta + 1}{4}$ for
odd $\Delta$. -/
@[category research solved, AMS 5]
theorem erdos_149.variants.max_degree_le_three (V : Type) [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.maxDegree ≤ 3) :
    G.strongChromaticIndex ≤ 10 := by
  sorry

/-! ### Sharpness: the blow-up of `C₅` -/

/-- The blow-up `C₅[t]` of the 5-cycle: vertices are pairs `(i, j)` with `i : ZMod 5` and
`j < t`, and `(i, j)` is adjacent to `(i', j')` iff `i' = i ± 1`. -/
def c5Blowup (t : ℕ) : SimpleGraph (ZMod 5 × Fin t) where
  Adj p q := p.1 - q.1 = 1 ∨ q.1 - p.1 = 1
  symm := fun _ _ h => h.symm
  loopless := ⟨fun p h => by simp at h; revert h; decide⟩

instance (t : ℕ) : DecidableRel (c5Blowup t).Adj :=
  fun p q => inferInstanceAs (Decidable (p.1 - q.1 = 1 ∨ q.1 - p.1 = 1))

@[category API, AMS 5]
lemma c5Blowup_degree (t : ℕ) (p : ZMod 5 × Fin t) : (c5Blowup t).degree p = 2 * t := by
  rw [← card_neighborFinset_eq_degree]
  have : (c5Blowup t).neighborFinset p =
      (univ.filter (fun a : ZMod 5 => p.1 - a = 1 ∨ a - p.1 = 1)) ×ˢ (univ : Finset (Fin t)) := by
    ext q
    simp [c5Blowup]
  rw [this, card_product, card_univ, Fintype.card_fin]
  congr 1
  generalize p.1 = x
  revert x
  decide

/-- `C₅[t]` has maximum degree `2t`. -/
@[category API, AMS 5]
theorem c5Blowup_maxDegree (t : ℕ) : (c5Blowup t).maxDegree = 2 * t := by
  refine le_antisymm ((c5Blowup t).maxDegree_le_of_forall_degree_le _
    (fun p => (c5Blowup_degree t p).le)) ?_
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · rw [← c5Blowup_degree t (0, ⟨0, ht⟩)]
    exact (c5Blowup t).degree_le_maxDegree _

@[category API, AMS 5]
lemma c5Blowup_card_edgeSet (t : ℕ) : Fintype.card (c5Blowup t).edgeSet = 5 * t ^ 2 := by
  have h := (c5Blowup t).sum_degrees_eq_twice_card_edges
  simp only [c5Blowup_degree, sum_const, card_univ, Fintype.card_prod, ZMod.card,
    Fintype.card_fin, smul_eq_mul] at h
  rw [← edgeFinset_card]
  nlinarith

/-- In `C₅[t]` no two edges are strongly independent. -/
@[category API, AMS 5]
lemma c5Blowup_not_stronglyIndependent (t : ℕ) (e f : (c5Blowup t).edgeSet) :
    ¬ (c5Blowup t).StronglyIndependent e.1 f.1 := by
  obtain ⟨e, he⟩ := e
  obtain ⟨f, hf⟩ := f
  induction e using Sym2.ind with
  | _ p q =>
  induction f using Sym2.ind with
  | _ r s =>
  intro h
  have hpq : (c5Blowup t).Adj p q := he
  have hrs : (c5Blowup t).Adj r s := hf
  have key : ∀ a b c d : ZMod 5, (a - b = 1 ∨ b - a = 1) → (c - d = 1 ∨ d - c = 1) →
      (a - c = 1 ∨ c - a = 1) ∨ (a - d = 1 ∨ d - a = 1) ∨ (b - c = 1 ∨ c - b = 1) ∨
      (b - d = 1 ∨ d - b = 1) := by decide
  rcases key p.1 q.1 r.1 s.1 hpq hrs with k | k | k | k
  · exact (h p (Sym2.mem_mk_left _ _) r (Sym2.mem_mk_left _ _)).2 k
  · exact (h p (Sym2.mem_mk_left _ _) s (Sym2.mem_mk_right _ _)).2 k
  · exact (h q (Sym2.mem_mk_right _ _) r (Sym2.mem_mk_left _ _)).2 k
  · exact (h q (Sym2.mem_mk_right _ _) s (Sym2.mem_mk_right _ _)).2 k

/-- `sq(C₅[t]) = 5t²`. -/
@[category API, AMS 5]
theorem c5Blowup_strongChromaticIndex (t : ℕ) :
    (c5Blowup t).strongChromaticIndex = 5 * t ^ 2 := by
  rw [(c5Blowup t).strongChromaticIndex_eq_card_of_forall_not_stronglyIndependent
    (fun e f _ => c5Blowup_not_stronglyIndependent t e f), c5Blowup_card_edgeSet]

/-- The constant $\frac{5}{4}$ in `erdos_149` cannot be lowered: the blow-up $C_5[t]$, in which
every vertex of $C_5$ is replaced by $t$ independent vertices, has $\Delta = 2t$ and
$sq(C_5[t]) = 5t^2 = \frac{5}{4}\Delta^2$. -/
@[category textbook, AMS 5]
theorem erdos_149.variants.sharp (t : ℕ) :
    ((c5Blowup t).strongChromaticIndex : ℝ) = 5 / 4 * ((c5Blowup t).maxDegree : ℝ) ^ 2 := by
  rw [c5Blowup_strongChromaticIndex, c5Blowup_maxDegree]
  push_cast
  ring

end Erdos149
