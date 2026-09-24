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
# The overfull conjecture (Chetwynd–Hilton 1986)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Overfull_graph)
* [CH86] Chetwynd, A. G. and Hilton, A. J. W. (1986). "Star multigraphs with three vertices of
  maximum degree." *Math. Proc. Cambridge Philos. Soc.* 100, pp. 303--317.
* [Vi64] Vizing, V. G. (1964). "On an estimate of the chromatic class of a p-graph."
  *Diskret. Analiz* 3, pp. 25--30.
* [CKLOT16] Csaba, B., Kühn, D., Lo, A., Osthus, D. and Treglown, A. (2016). "Proof of the
  1-factorization and Hamilton decomposition conjectures." *Mem. Amer. Math. Soc.* 244.
  [arXiv:1401.4159](https://arxiv.org/abs/1401.4159)
* [Pl98] Plantholt, M. (1998). "Overfull conjecture for graphs with high minimum degree."
  *J. Graph Theory* 47, pp. 73--80.
-/

open SimpleGraph Finset

namespace OverfullConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is **overfull** if it has more than $\Delta \lfloor n/2 \rfloor$ edges, so that no
$\Delta$ colour classes (each a matching of size at most $\lfloor n/2 \rfloor$) can cover it. -/
def IsOverfull (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.maxDegree * (Fintype.card V / 2) < G.edgeFinset.card

open Classical in
/-- `G` **contains an overfull subgraph of the same maximum degree**: some induced subgraph on a
vertex set `S` is overfull and has maximum degree `Δ(G)`. -/
def HasOverfullSubgraph (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ S : Finset V, (G.induce (S : Set V)).maxDegree = G.maxDegree ∧
    IsOverfull (G.induce (S : Set V))

/--
**The overfull conjecture (Chetwynd–Hilton 1986).**

If $\Delta(G) > n/3$ then $G$ is class $1$ (its chromatic index equals $\Delta(G)$) if and
only if $G$ contains no overfull subgraph with the same maximum degree.
-/
@[category research open, AMS 5]
theorem overfull_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V < 3 * G.maxDegree →
      (G.chromaticIndex = G.maxDegree ↔ ¬ HasOverfullSubgraph G) := by
  sorry

/--
**Vizing's theorem (1964).**

Every finite simple graph satisfies $\Delta(G) \le \chi'(G) \le \Delta(G) + 1$.

*Reference:* [Vi64].
-/
@[category research solved, AMS 5]
theorem overfull_conjecture.variants.vizing
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.maxDegree ≤ G.chromaticIndex ∧ G.chromaticIndex ≤ G.maxDegree + 1 := by
  sorry

/--
**The 1-factorization conjecture (proved for large $n$ by Csaba, Kühn, Lo, Osthus and
Treglown 2016).**

Every $d$-regular graph on an even number $n$ of vertices with $d \ge 2\lceil n/4 \rceil - 1$
is class $1$, i.e. decomposes into perfect matchings. The overfull conjecture would imply this
for all $n$.

*Reference:* [CKLOT16].
-/
@[category research solved, AMS 5]
theorem overfull_conjecture.variants.one_factorization :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (d : ℕ), n₀ ≤ Fintype.card V → Even (Fintype.card V) → (∀ v, G.degree v = d) →
      2 * ((Fintype.card V + 3) / 4) - 1 ≤ d → G.chromaticIndex = d := by
  sorry


/-- The vertices of a non-diagonal `e : Sym2 V` form a `2`-element finset. -/
@[category API, AMS 5]
lemma card_filter_mem_sym2 {e : Sym2 V} (he : ¬ e.IsDiag) :
    (Finset.univ.filter fun v => v ∈ e).card = 2 := by
  induction e using Sym2.ind with
  | h x y =>
    rw [Sym2.mk_isDiag_iff] at he
    rw [show (Finset.univ.filter fun v => v ∈ s(x, y)) = {x, y} by ext v; simp [Sym2.mem_iff]]
    exact Finset.card_pair he

/-- A colour class of a proper edge colouring consists of pairwise disjoint edges, hence has at
most `⌊n / 2⌋` edges. -/
@[category API, AMS 5]
lemma card_colour_class_le (G : SimpleGraph V) [DecidableRel G.Adj] {α : Type*} [DecidableEq α]
    {c : Sym2 V → α} (hc : G.IsProperEdgeColoring c) (a : α) :
    (G.edgeFinset.filter fun e => c e = a).card ≤ Fintype.card V / 2 := by
  set S := G.edgeFinset.filter fun e => c e = a with hS
  have hmem : ∀ e ∈ S, e ∈ G.edgeSet := fun e he => mem_edgeFinset.mp (Finset.mem_filter.mp he).1
  have h2 : ∀ e ∈ S, (Finset.univ.filter fun v => v ∈ e).card = 2 :=
    fun e he => card_filter_mem_sym2 (G.not_isDiag_of_mem_edgeSet (hmem e he))
  have hdisj : (S : Set (Sym2 V)).PairwiseDisjoint fun e => Finset.univ.filter fun v => v ∈ e := by
    intro e he f hf hef
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
    exact hc e (hmem e he) f (hmem f hf) hef ⟨v, hv, hv'⟩
      ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  have hsum : 2 * S.card = (S.biUnion fun e => Finset.univ.filter fun v => v ∈ e).card := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hle : (S.biUnion fun e => Finset.univ.filter fun v => v ∈ e).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  omega

/--
**An overfull graph is class 2.**

If $G$ is overfull then $\chi'(G) > \Delta(G)$: each colour class is a matching with at most
$\lfloor n/2 \rfloor$ edges. This is the easy direction of the conjecture (with $S = V$).
-/
@[category research solved, AMS 5]
theorem overfull_conjecture.variants.class_two_of_isOverfull
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : IsOverfull G) : G.maxDegree < G.chromaticIndex := by
  by_contra hle
  push Not at hle
  -- The chromatic index is attained by some proper edge colouring.
  have hne : {n | G.EdgeColorable n}.Nonempty := ⟨_, G.edgeColorable_card_edgeFinset_succ⟩
  obtain ⟨c, hc⟩ : G.EdgeColorable G.chromaticIndex := Nat.sInf_mem hne
  -- Count the edges fibrewise over the colours.
  have hcount : G.edgeFinset.card =
      ∑ a : Fin G.chromaticIndex, (G.edgeFinset.filter fun e => c e = a).card :=
    Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _
  have hbound : G.edgeFinset.card ≤ G.chromaticIndex * (Fintype.card V / 2) := by
    rw [hcount]
    calc ∑ a : Fin G.chromaticIndex, (G.edgeFinset.filter fun e => c e = a).card
        ≤ ∑ _a : Fin G.chromaticIndex, Fintype.card V / 2 :=
          Finset.sum_le_sum fun a _ => card_colour_class_le G hc a
      _ = G.chromaticIndex * (Fintype.card V / 2) := by simp
  unfold IsOverfull at h
  have := Nat.mul_le_mul_right (Fintype.card V / 2) hle
  omega

end OverfullConjecture
