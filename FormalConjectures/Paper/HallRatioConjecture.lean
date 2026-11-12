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
# The Hall ratio conjecture (Harris 2019) — disproved

*References:*
* [Ha19] Harris, D. G. (2019). "Some results on chromatic number as a function of triangle
  count." *SIAM J. Discrete Math.* 33, pp. 546--563.
* [DOW20] Dvořák, Z., Ossona de Mendez, P. and Wu, H. (2020). "1-subdivisions, the fractional
  chromatic number and the Hall ratio." *Combinatorica* 40, pp. 759--774.
  [arXiv:1812.07327](https://arxiv.org/abs/1812.07327)
* [BLMNPV22] Blumenthal, A., Lidický, B., Martin, R. R., Norin, S., Pfender, F. and Volec, J.
  (2022). "Counterexamples to a conjecture of Harris on Hall ratio." *SIAM J. Discrete Math.*
  36, pp. 1678--1686. [arXiv:1811.11116](https://arxiv.org/abs/1811.11116)
* [SU97] Scheinerman, E. R. and Ullman, D. H. (1997). *Fractional Graph Theory.* Wiley.
-/

@[expose] public section

open SimpleGraph

namespace HallRatioConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **Hall ratio** `ρ(G)`: the maximum of `|V(H)| / α(H)` over nonempty induced subgraphs
`H` of `G` (`α` the independence number). -/
noncomputable def hallRatio (G : SimpleGraph V) : ℝ :=
  sSup {r | ∃ S : Finset V, S.Nonempty ∧
    r = (S.card : ℝ) / ((G.induce (S : Set V)).indepNum : ℝ)}

/--
**The Hall ratio conjecture (Harris 2019) — disproved.**

Harris conjectured that the fractional chromatic number is bounded by a constant multiple of the
Hall ratio: there is a constant $C$ with $\chi_f(G) \le C\,\rho(G)$ for every graph $G$. This
is **false**: Dvořák, Ossona de Mendez and Wu [DOW20] and, independently, Blumenthal, Lidický,
Martin, Norin, Pfender and Volec [BLMNPV22] constructed graphs with $\chi_f / \rho$
arbitrarily large.
-/
@[category research solved, AMS 5]
theorem hall_ratio_conjecture : ¬
    ∃ C : ℝ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.fractionalChromaticNumber ≤ C * hallRatio G := by
  sorry

/-- An independent set of `G` meets `S` in at most `α(G[S])` vertices. -/
@[category API, AMS 5]
theorem card_filter_le_indepNum {G : SimpleGraph V} {T : Finset V}
    (hT : G.IsIndepSet (T : Set V)) (S : Finset V) :
    (S.filter (· ∈ T)).card ≤ (G.induce (S : Set V)).indepNum := by
  let t := (S.filter (· ∈ T)).subtype (· ∈ (S : Set V))
  have ht : (G.induce (S : Set V)).IsIndepSet (t : Set (S : Set V)) := by
    intro x hx y hy hxy
    simp only [t, Finset.mem_coe, Finset.mem_subtype, Finset.mem_filter] at hx hy
    exact hT hx.2 hy.2 (Subtype.coe_injective.ne hxy)
  calc (S.filter (· ∈ T)).card = t.card := by
        rw [Finset.card_subtype, Finset.filter_true_of_mem (p := fun x => x ∈ (S : Set V))
          fun x hx => Finset.mem_coe.mpr (Finset.mem_filter.mp hx).1]
    _ ≤ _ := ht.card_le_indepNum

/-- Double counting: `|S| ≤ α(G[S]) · t` for a fractional colouring of total weight `t`. -/
@[category API, AMS 5]
theorem card_le_indepNum_mul {G : SimpleGraph V} {w : Finset V → ℝ}
    (hw : G.IsFractionalColoring w) (S : Finset V) :
    (S.card : ℝ) ≤ (G.induce (S : Set V)).indepNum * ∑ T, w T := by
  calc (S.card : ℝ) = ∑ _v ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ S, ∑ T ∈ Finset.univ.filter (fun T => v ∈ T), w T :=
        Finset.sum_le_sum fun v _ => hw.cover v
    _ = ∑ T, ∑ v ∈ S, if v ∈ T then w T else 0 := by
        simp_rw [Finset.sum_filter]
        exact Finset.sum_comm
    _ = ∑ T, ((S.filter (· ∈ T)).card : ℝ) * w T := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ T, ((G.induce (S : Set V)).indepNum : ℝ) * w T := by
        refine Finset.sum_le_sum fun T _ => ?_
        by_cases h : w T = 0
        · simp [h]
        · exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast card_filter_le_indepNum (hw.indep T h) S) (hw.nonneg T)
    _ = _ := by rw [Finset.mul_sum]

/-- Each ratio `|S| / α(G[S])` is at most the total weight of any fractional colouring. -/
@[category API, AMS 5]
theorem div_indepNum_le {G : SimpleGraph V} {w : Finset V → ℝ}
    (hw : G.IsFractionalColoring w) (S : Finset V) :
    (S.card : ℝ) / (G.induce (S : Set V)).indepNum ≤ ∑ T, w T := by
  rcases Nat.eq_zero_or_pos (G.induce (S : Set V)).indepNum with h | h
  · simpa [h] using Finset.sum_nonneg fun T _ => hw.nonneg T
  · rw [div_le_iff₀ (by exact_mod_cast h), mul_comm]
    exact card_le_indepNum_mul hw S

/--
**The Hall ratio is a lower bound for the fractional chromatic number.**

For every graph, $\rho(G) \le \chi_f(G)$ (see [SU97]); the conjecture asked for an inequality in
the other direction up to a constant.
-/
@[category research solved, AMS 5]
theorem hall_ratio_conjecture.variants.hallRatio_le_fractionalChromaticNumber
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    hallRatio G ≤ G.fractionalChromaticNumber := by
  refine Real.sSup_le ?_ G.fractionalChromaticNumber_nonneg
  rintro r ⟨S, -, rfl⟩
  refine le_csInf G.fractionalColoringWeights_nonempty ?_
  rintro t ⟨w, hw, rfl⟩
  exact div_indepNum_le hw S

/--
**Unbounded ratio (Dvořák–Ossona de Mendez–Wu 2020; Blumenthal et al. 2022).**

For every $C$ there is a graph with $\chi_f(G) > C\,\rho(G)$.

*References:* [DOW20], [BLMNPV22].
-/
@[category research solved, AMS 5]
theorem hall_ratio_conjecture.variants.unbounded (C : ℝ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      C * hallRatio G < G.fractionalChromaticNumber := by
  sorry

end HallRatioConjecture
