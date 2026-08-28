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
# The Bollobás–Eldridge–Catlin conjecture on graph packing (1978)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Graph_packing)
* [BE78] Bollobás, B. and Eldridge, S. E. (1978). "Packings of graphs and applications to
  computational complexity." *J. Combin. Theory Ser. B* 25, pp. 105--124.
* [Ca74] Catlin, P. A. (1974). "Subgraphs of graphs, I." *Discrete Math.* 10, pp. 225--233.
* [SS78] Sauer, N. and Spencer, J. (1978). "Edge disjoint placement of graphs."
  *J. Combin. Theory Ser. B* 25, pp. 295--302.
* [AF93] Aigner, M. and Brandt, S. (1993). "Embedding arbitrary graphs of maximum degree two."
  *J. London Math. Soc.* 48, pp. 39--51.
* [CSS03] Csaba, B., Shokoufandeh, A. and Szemerédi, E. (2003). "Proof of a conjecture of
  Bollobás and Eldridge for graphs of maximum degree three." *Combinatorica* 23, pp. 35--72.
-/

open SimpleGraph

namespace BollobasEldridgeCatlinConjecture

variable {V : Type*}

/-- Two graphs `G₁`, `G₂` on the same finite vertex set **pack** if some permutation of the
vertices makes their edge sets disjoint. -/
def Packs (G₁ G₂ : SimpleGraph V) : Prop :=
  ∃ σ : Equiv.Perm V, ∀ u v, G₁.Adj u v → ¬ G₂.Adj (σ u) (σ v)

/--
**The Bollobás–Eldridge–Catlin conjecture (1978).**

If $G_1$ and $G_2$ are graphs on the same $n$ vertices with maximum degrees $\Delta_1$,
$\Delta_2$ satisfying $(\Delta_1 + 1)(\Delta_2 + 1) \le n + 1$, then $G_1$ and $G_2$ pack.
-/
@[category research open, AMS 5]
theorem bollobas_eldridge_catlin_conjecture : answer(sorry) ↔
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
      [DecidableRel G₁.Adj] [DecidableRel G₂.Adj],
      (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1 → Packs G₁ G₂ := by
  sorry

/--
**The Sauer–Spencer theorem (1978).**

If $2\Delta_1\Delta_2 < n$ then $G_1$ and $G_2$ pack.

*Reference:* [SS78].
-/
@[category research solved, AMS 5]
theorem bollobas_eldridge_catlin_conjecture.variants.sauer_spencer
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) : Packs G₁ G₂ := by
  sorry

/--
**Maximum degree two (Aigner–Brandt 1993) and three (Csaba–Shokoufandeh–Szemerédi 2003).**

The conjecture holds whenever one of the graphs has maximum degree at most $3$ (for
$\Delta_1 = 3$ only for sufficiently large $n$ in [CSS03]).

*References:* [AF93], [CSS03].
-/
@[category research solved, AMS 5]
theorem bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2)
    (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) : Packs G₁ G₂ := by
  sorry

/-- Packing is symmetric. -/
@[category API, AMS 5]
lemma Packs.symm {G₁ G₂ : SimpleGraph V} (h : Packs G₁ G₂) : Packs G₂ G₁ := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, fun u v huv h₁ => hσ (σ.symm u) (σ.symm v) h₁ ?_⟩
  simpa using huv

/-- Every graph packs with the empty graph. -/
@[category API, AMS 5]
lemma packs_bot (G : SimpleGraph V) : Packs G ⊥ :=
  ⟨1, fun _ _ _ h => h⟩

/--
**The case where one graph has no edges.**

If $\Delta_2 = 0$ then $G_2$ is edgeless and the conjecture holds trivially.
-/
@[category research solved, AMS 5]
theorem bollobas_eldridge_catlin_conjecture.variants.edgeless
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : G₂.maxDegree = 0) : Packs G₁ G₂ := by
  refine ⟨1, fun u v _ huv => ?_⟩
  have : G₂.degree (u) ≠ 0 := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_ne_zero.mpr ⟨v, by simpa using huv⟩
  exact this (Nat.le_zero.mp (h ▸ G₂.degree_le_maxDegree u))

end BollobasEldridgeCatlinConjecture
