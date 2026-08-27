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
# Vizing's conjecture (1968)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Vizing%27s_conjecture)
* [Vi68] Vizing, V. G. (1968). "Some unsolved problems in graph theory."
  *Uspekhi Mat. Nauk* 23, pp. 117--134.
* [ClSu00] Clark, W. E. and Suen, S. (2000). "An inequality related to Vizing's conjecture."
  *Electron. J. Combin.* 7, N4.
* [SuTa12] Suen, S. and Tarr, J. (2012). "An improved inequality related to Vizing's conjecture."
  *Electron. J. Combin.* 19, P8.
* [BDGHHKR12] Brešar, B., Dorbec, P., Goddard, W., Hartnell, B. L., Henning, M. A., Klavžar, S.
  and Rall, D. F. (2012). "Vizing's conjecture: a survey and recent results."
  *J. Graph Theory* 69, pp. 46--76.
-/

open SimpleGraph

namespace VizingConjecture

/--
**Vizing's conjecture (1968).**

For all finite simple graphs $G$ and $H$, the domination number of the Cartesian (box)
product satisfies $\gamma(G \,\square\, H) \ge \gamma(G)\,\gamma(H)$.
-/
@[category research open, AMS 5]
theorem vizing_conjecture : answer(sorry) ↔
    ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (G : SimpleGraph α) (H : SimpleGraph β),
      G.dominationNumber * H.dominationNumber ≤ (G □ H).dominationNumber := by
  sorry

/--
**The Clark–Suen inequality (2000).**

For all finite simple graphs $G$ and $H$,
$\gamma(G \,\square\, H) \ge \tfrac12\,\gamma(G)\,\gamma(H)$; that is, Vizing's conjecture holds
up to a factor of $2$.

*Reference:* [ClSu00].
-/
@[category research solved, AMS 5]
theorem vizing_conjecture.variants.clark_suen
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    G.dominationNumber * H.dominationNumber ≤ 2 * (G □ H).dominationNumber := by
  sorry

/--
**The Suen–Tarr inequality (2012).**

For all finite simple graphs $G$ and $H$,
$\gamma(G \,\square\, H) \ge \tfrac12\,\gamma(G)\,\gamma(H) +
\tfrac12\min\{\gamma(G), \gamma(H)\}$, improving the Clark–Suen bound.

*Reference:* [SuTa12].
-/
@[category research solved, AMS 5]
theorem vizing_conjecture.variants.suen_tarr
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    G.dominationNumber * H.dominationNumber + min G.dominationNumber H.dominationNumber ≤
      2 * (G □ H).dominationNumber := by
  sorry

/-- The set `Finset.univ` is a dominating set of any graph, so the set of sizes of dominating
sets is nonempty and `dominationNumber` is attained by some dominating set. -/
@[category API, AMS 5]
lemma exists_isNDominatingSet_dominationNumber {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) :
    ∃ D : Finset α, G.IsNDominatingSet G.dominationNumber D := by
  have hne : {n | ∃ D : Finset α, G.IsNDominatingSet n D}.Nonempty :=
    ⟨_, Finset.univ, ⟨fun v => Or.inl (Finset.mem_univ v), rfl⟩⟩
  exact Nat.sInf_mem hne

/-- If `D` is a dominating set of `G` with `n` elements then `γ(G) ≤ n`. -/
@[category API, AMS 5]
lemma dominationNumber_le_of_isDominating {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (D : Finset α) (hD : G.IsDominating D) :
    G.dominationNumber ≤ D.card :=
  Nat.sInf_le ⟨D, hD, rfl⟩

/--
**Projection bound: `γ(G) ≤ γ(G □ H)` whenever `H` has a vertex.**

Projecting a dominating set of `G □ H` onto the first coordinate yields a dominating set of
`G` of no larger size: a vertex `(v, b)` is dominated by some `(w, c)` with either `v = w`
(so `v` lies in the projection) or `G.Adj v w` (so `v` is dominated by `w` in the projection).
-/
@[category API, AMS 5]
theorem dominationNumber_le_dominationNumber_boxProd
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    G.dominationNumber ≤ (G □ H).dominationNumber := by
  obtain ⟨D, hD, hcard⟩ := exists_isNDominatingSet_dominationNumber (G □ H)
  refine le_trans (dominationNumber_le_of_isDominating G (D.image Prod.fst) ?_) ?_
  · intro v
    obtain ⟨b⟩ := ‹Nonempty β›
    rcases hD (v, b) with h | ⟨⟨w, c⟩, hw, hadj⟩
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst (Finset.mem_coe.mp h)))
    · rw [boxProd_adj] at hadj
      rcases hadj with ⟨hvw, -⟩ | ⟨-, hvw⟩
      · exact Or.inr ⟨w, Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst (Finset.mem_coe.mp hw)),
          hvw⟩
      · obtain rfl : v = w := hvw
        exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst (Finset.mem_coe.mp hw)))
  · exact hcard ▸ Finset.card_image_le

/--
**Vizing's conjecture when `γ(H) = 1`.**

If `H` has a dominating vertex, so that $\gamma(H) = 1$, then Vizing's inequality reduces to
$\gamma(G) \le \gamma(G \,\square\, H)$, which is the projection bound
`dominationNumber_le_dominationNumber_boxProd`. This is the simplest of the known cases of the
conjecture (see [BDGHHKR12]).
-/
@[category research solved, AMS 5]
theorem vizing_conjecture.variants.dominationNumber_eq_one
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) (hH : H.dominationNumber = 1) :
    G.dominationNumber * H.dominationNumber ≤ (G □ H).dominationNumber := by
  -- `γ(H) = 1` forces `H` to have a vertex: the empty graph has `γ = 0`.
  have hne : Nonempty β := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : H.dominationNumber = 0 :=
      Nat.le_zero.mp (dominationNumber_le_of_isDominating H ∅ (fun v => (IsEmpty.false v).elim))
    omega
  rw [hH, mul_one]
  exact dominationNumber_le_dominationNumber_boxProd G H

end VizingConjecture
