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
# Alspach's conjecture on cycle decompositions of complete graphs (1981; proved 2014)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Alspach%27s_conjecture)
* [Al81] Alspach, B. (1981). "Research problems, Problem 3." *Discrete Math.* 36, p. 333.
* [BHP14] Bryant, D., Horsley, D. and Pettersson, W. (2014). "Cycle decompositions V:
  Complete graphs into cycles of arbitrary lengths." *Proc. London Math. Soc.* 108,
  pp. 1153--1192. [arXiv:1204.3709](https://arxiv.org/abs/1204.3709)
* [GJKKO21] Glock, S., Joos, F., Kim, J., Kühn, D. and Osthus, D. (2021). "Resolution of the
  Oberwolfach problem." *J. Eur. Math. Soc.* 23, pp. 2511--2547.
  [arXiv:1806.04644](https://arxiv.org/abs/1806.04644)
* [BH09] Bryant, D. and Horsley, D. (2009). "Decompositions of complete graphs into long
  cycles." *Bull. London Math. Soc.* 41, pp. 927--934.
-/

open SimpleGraph Finset

namespace AlspachConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- A multiset of cycles `C` is a **cycle decomposition** of `G` if every edge of `G` lies on
exactly one of the cycles. -/
def IsCycleDecomposition (G : SimpleGraph V) [DecidableRel G.Adj] (C : Multiset (Cycle G)) :
    Prop :=
  ∀ e ∈ G.edgeFinset, (C.filter fun c => e ∈ c.edges).card = 1

/-- The multiset of cycle lengths of a family of cycles. -/
def lengths {G : SimpleGraph V} (C : Multiset (Cycle G)) : Multiset ℕ :=
  C.map SimpleGraph.Cycle.length

/--
**Alspach's conjecture (1981), proved by Bryant, Horsley and Pettersson (2014).**

Let $n$ be odd and let $m_1, \dots, m_t$ be integers with $3 \le m_i \le n$ and
$m_1 + \dots + m_t = \binom{n}{2}$. Then the complete graph $K_n$ decomposes into cycles of
lengths $m_1, \dots, m_t$. (These conditions are clearly necessary: $K_n$ has all degrees even
only for odd $n$, and its edges must be split exactly among the cycles.)
-/
@[category research solved, AMS 5]
theorem alspach_conjecture : answer(True) ↔
    ∀ (n : ℕ), Odd n → ∀ m : Multiset ℕ, (∀ x ∈ m, 3 ≤ x ∧ x ≤ n) → m.sum = n.choose 2 →
      ∃ C : Multiset (Cycle (completeGraph (Fin n))),
        IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m := by
  sorry

open Classical in
/--
**The even case (Bryant–Horsley–Pettersson 2014).**

For even $n$, the complete graph minus a perfect matching, $K_n - I$, decomposes into cycles of
lengths $m_1, \dots, m_t$ whenever $3 \le m_i \le n$ and $\sum m_i = \binom{n}{2} - n/2$.
Since Mathlib has no canonical perfect matching of $K_n$, we state this for any perfect
matching `I`.

*Reference:* [BHP14].
-/
@[category research solved, AMS 5]
theorem alspach_conjecture.variants.even (n : ℕ) (hn : Even n)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (m : Multiset ℕ) (hm : ∀ x ∈ m, 3 ≤ x ∧ x ≤ n) (hsum : m.sum = n.choose 2 - n / 2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition (completeGraph (Fin n) \ I.spanningCoe) C ∧ lengths C = m := by
  sorry

/--
**Long cycles (Bryant–Horsley 2009).**

The conjecture holds (for odd $n$) whenever all the prescribed lengths $m_i$ are at least
$\lceil n/2 \rceil$.

*Reference:* [BH09].
-/
@[category research solved, AMS 5]
theorem alspach_conjecture.variants.long_cycles (n : ℕ) (hn : Odd n) (m : Multiset ℕ)
    (hm : ∀ x ∈ m, (n + 1) / 2 ≤ x ∧ x ≤ n) (hsum : m.sum = n.choose 2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n))),
      IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m := by
  sorry

/-- The empty family decomposes an edgeless graph. -/
@[category API, AMS 5]
lemma isCycleDecomposition_zero {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.edgeFinset = ∅) : IsCycleDecomposition G 0 :=
  fun e he => by simp [h] at he

/--
**The case $n = 1$.**

$K_1$ has no edges, so the only admissible multiset of lengths is empty and the empty
decomposition works.
-/
@[category test, AMS 5]
theorem alspach_conjecture.variants.one (m : Multiset ℕ) (hm : ∀ x ∈ m, 3 ≤ x ∧ x ≤ 1)
    (hsum : m.sum = Nat.choose 1 2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin 1))),
      IsCycleDecomposition (completeGraph (Fin 1)) C ∧ lengths C = m := by
  have hm0 : m = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    have := hm x hx
    omega
  subst hm0
  refine ⟨0, isCycleDecomposition_zero ?_, Multiset.map_zero _⟩
  decide

/-- The triangle `0 → 1 → 2 → 0` as a cycle of `K₃`. -/
def triangle : Cycle (completeGraph (Fin 3)) where
  base := 0
  walk := Walk.cons (by decide : (completeGraph (Fin 3)).Adj 0 1)
    (Walk.cons (by decide : (completeGraph (Fin 3)).Adj 1 2)
      (Walk.cons (by decide : (completeGraph (Fin 3)).Adj 2 0) Walk.nil))
  isCycle := by
    rw [Walk.isCycle_def, Walk.isTrail_def]
    exact ⟨by decide, by simp, by decide⟩

/--
**The case $n = 3$.**

$K_3$ has three edges, so the only admissible multiset of lengths is $\{3\}$, realised by the
triangle itself.
-/
@[category test, AMS 5]
theorem alspach_conjecture.variants.three (m : Multiset ℕ) (hm : ∀ x ∈ m, 3 ≤ x ∧ x ≤ 3)
    (hsum : m.sum = Nat.choose 3 2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin 3))),
      IsCycleDecomposition (completeGraph (Fin 3)) C ∧ lengths C = m := by
  -- Every element of `m` is `3`, and the sum is `3`, so `m = {3}`.
  have hm3 : m = Multiset.replicate m.card 3 := by
    rw [Multiset.eq_replicate]; exact ⟨rfl, fun x hx => le_antisymm (hm x hx).2 (hm x hx).1⟩
  have hcard : m.card = 1 := by
    have := hsum; rw [hm3, Multiset.sum_replicate, smul_eq_mul] at this; simp at this; omega
  rw [hm3, hcard, Multiset.replicate_one]
  refine ⟨{triangle}, fun e he => ?_, by simp [lengths, triangle]; decide⟩
  rw [Multiset.filter_singleton]
  split_ifs with h
  · rfl
  · exfalso
    apply h
    have he' : e ∈ (completeGraph (Fin 3)).edgeSet := mem_edgeFinset.mp he
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet, completeGraph_eq_top, top_adj] at he'
      fin_cases a <;> fin_cases b <;> first | exact absurd rfl he' | decide

/-- The exceptional Oberwolfach $2$-factor `C₄ + C₅` on nine vertices. -/
def oberwolfachException9 : SimpleGraph (Fin 4 ⊕ Fin 5) :=
  cycleGraph 4 ⊕g cycleGraph 5

/-- The exceptional Oberwolfach $2$-factor `C₃ + C₃ + C₅` on eleven vertices. -/
def oberwolfachException11 : SimpleGraph ((Fin 3 ⊕ Fin 3) ⊕ Fin 5) :=
  (cycleGraph 3 ⊕g cycleGraph 3) ⊕g cycleGraph 5

/--
**The Oberwolfach problem (Ringel 1967).**

For odd $n$ and a $2$-regular graph $F$ on $n$ vertices, can $K_n$ be decomposed into
$(n-1)/2$ spanning subgraphs isomorphic to $F$? The decomposition is known to be impossible for
exactly two pairs with odd $n$ — $(9, C_4 + C_5)$ and $(11, C_3 + C_3 + C_5)$ — and is
conjectured to exist in every other case. Known for all sufficiently large $n$ [GJKKO21].
-/
@[category research open, AMS 5]
theorem alspach_conjecture.variants.oberwolfach : answer(sorry) ↔
    ∀ (n : ℕ), Odd n → 3 ≤ n →
      ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj], (∀ v, F.degree v = 2) →
      IsEmpty (F ≃g oberwolfachException9) → IsEmpty (F ≃g oberwolfachException11) →
      ∃ D : Fin ((n - 1) / 2) → SimpleGraph (Fin n),
        (∀ i, Nonempty (D i ≃g F)) ∧
        ∀ u v, (completeGraph (Fin n)).Adj u v ↔ ∃! i, (D i).Adj u v := by
  sorry

end AlspachConjecture
