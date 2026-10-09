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
# Erdős Problem 500

*References:*
- [erdosproblems.com/500](https://www.erdosproblems.com/500)
- [Ra10] Razborov, Alexander A., On 3-hypergraphs with forbidden 4-vertex configurations. SIAM J.
  Discrete Math. (2010), 946-963.
- [BaTa11] Baber, Rahil and Talbot, John, *Hypergraphs do jump*. Combin. Probab. Comput. (2011),
  161-171.
- [Ba12] Baber, Rahil, *Turán densities of hypercubes*. arXiv:1201.3587 (2012).
- [JPILY26] Jeong, Gyeongwon and Park, Seonghun and Im, Seonghyuk and Lee, Joonkyung and Yang,
  Hongseok, *A New Upper Bound for the Turán Density of the Tetrahedron*. arXiv:2609.27495
  (2026).
-/

@[expose] public section

namespace Erdos500

open Filter Asymptotics
open scoped Topology

/--
What is $\mathrm{ex}_3(n,K_4^3)$? That is, the largest number of $3$-edges which can placed on $n$
vertices so that there exists no $K_4^3$, a set of 4 vertices which is covered by all 4 possible
$3$-edges.

See also [712](https://www.erdosproblems.com/712) for the general case.
-/
@[category research open, AMS 5]
theorem erdos_500 :
    (fun n ↦ Hypergraph.cliqueExtremalNumber n 3 4) = answer(sorry) := by
  sorry

/--
A problem of Turán. Turán observed that dividing the vertices into three equal parts
$X_1,X_2,X_3$, and taking the edges to be those triples that either have exactly one vertex in
each part or two vertices in $X_i$ and one vertex in $X_{i+1}$ (where $X_4=X_1$) shows that
$$\mathrm{ex}_3(n,K_4^3)\geq\left(\frac{5}{9}+o(1)\right)\binom{n}{3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_500.variants.lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  sorry

/--
Turán observed that dividing the vertices into three equal parts $X_1,X_2,X_3$, and taking the
edges to be those triples that either have exactly one vertex in each part or two vertices in
$X_i$ and one vertex in $X_{i+1}$ (where $X_4=X_1$) shows that
$$\mathrm{ex}_3(n,K_4^3)\geq\left(\frac{5}{9}+o(1)\right)\binom{n}{3}.$$
This is probably the truth.
-/
@[category research open, AMS 5]
theorem erdos_500.variants.turan_conjecture :
    (fun n ↦ (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ)) ~[atTop]
      fun n ↦ 5 / 9 * (n.choose 3 : ℝ) := by
  sorry

/--
The current best upper bound is
$$\mathrm{ex}_3(n,K_4^3)\leq (0.561666+o(1))\binom{n}{3},$$
due to Razborov [Ra10]. (erdosproblems.com gives $0.5611666$ and omits the $o(1)$; without it
the bound fails at $n=4$, where $\mathrm{ex}_3(4,K_4^3)=3>0.561666\binom{4}{3}$.)

[Ra10, (2)] gives this bound in complementary form, as a result that numerical computations
suggest, not as a theorem. [BaTa11] reproduce the computation.

This is no longer the best bound: Baber [Ba12, §5.1] gives $\pi(K_4^3)\leq 0.5615$, where
$\pi(K_4^3)$ is the Turán density of `erdos_500.variants.asymptotic`. Jeong, Park, Im, Lee and
Yang [JPILY26, Theorem 1.1] prove that $\pi(K_4^3)<0.557789$, with a formal proof in Lean 4.
The bound above follows from this result.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/taeyool/tetrahedron-turan/blob/28b83b6f215cb886d2abdc89b33fdae3f17a7e3f/LeanFlagAlgebras/Core/Examples/FullSevenConverged/TetrahedronDifferential.lean#L251"]
theorem erdos_500.variants.upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) ≤ (0.561666 + ε) * (n.choose 3 : ℝ) := by
  sorry

/--
The asymptotic form of the question: what is the Turán density
$$\pi(K_4^3)=\lim_{n\to\infty}\frac{\mathrm{ex}_3(n,K_4^3)}{\binom{n}{3}}?$$
By `erdos_500.variants.lower_bound`, $\pi(K_4^3)\geq\frac{5}{9}$.
Turán's conjecture says that $\pi(K_4^3)=\frac{5}{9}$.
-/
@[category research open, AMS 5]
theorem erdos_500.variants.asymptotic :
    Tendsto (fun n : ℕ ↦ (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) / (n.choose 3 : ℝ))
      atTop (𝓝 answer(sorry)) := by
  sorry

/-- On three vertices the only possible edge is the whole vertex set, so
$\mathrm{ex}_3(3,K_4^3) = 1$. -/
@[category test, AMS 5]
theorem cliqueExtremalNumber_three : Hypergraph.cliqueExtremalNumber 3 3 4 = 1 := by
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply le_antisymm
  · refine Finset.sup_le fun H hH ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_powerset] at hH
    calc H.card ≤ ((Finset.univ : Finset (Fin 3)).powersetCard 3).card :=
          Finset.card_le_card hH.1
      _ = 1 := by simp [Finset.card_powersetCard]
  · refine le_trans ?_ (Finset.le_sup (f := Finset.card) (b := {Finset.univ}) ?_)
    · simp
    · simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        subst he
        simp [Finset.mem_powersetCard]
      · rintro ⟨S, hS, -⟩
        have := Finset.card_le_univ S
        rw [hS, Fintype.card_fin] at this
        omega

/-- On four vertices a $K_4^3$ is the set of all four $3$-edges, so $\mathrm{ex}_3(4,K_4^3) = 3$.
Unlike the case $n = 3$, this case depends on the condition that no $K_4^3$ is present. -/
@[category test, AMS 5]
theorem cliqueExtremalNumber_four : Hypergraph.cliqueExtremalNumber 4 3 4 = 3 := by
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply le_antisymm
  · refine Finset.sup_le fun H hH ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_powerset] at hH
    obtain ⟨hsub, hno⟩ := hH
    by_contra hlt
    have hcard : ((Finset.univ : Finset (Fin 4)).powersetCard 3).card = 4 := by
      simp [Finset.card_powersetCard]
    have hHeq : H = (Finset.univ : Finset (Fin 4)).powersetCard 3 :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hno ⟨Finset.univ, by simp, by rw [hHeq]⟩
  · let H0 : Finset (Finset (Fin 4)) := {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}}
    have hH0c : H0.card = 3 :=
      Finset.card_eq_three.mpr
        ⟨{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, by decide, by decide, by decide, rfl⟩
    refine le_trans hH0c.ge (Finset.le_sup (f := Finset.card) (b := H0) ?_)
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [H0, Finset.mem_insert, Finset.mem_singleton] at he
      rw [Finset.mem_powersetCard]
      rcases he with rfl | rfl | rfl <;> exact ⟨Finset.subset_univ _, rfl⟩
    · rintro ⟨S, hS, hsub⟩
      have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hS, Fintype.card_fin])
      subst hSu
      have := Finset.card_le_card hsub
      rw [hH0c, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at this
      exact absurd this (by decide)

end Erdos500
