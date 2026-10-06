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
- [Ra10] Razborov, Alexander A., *On 3-hypergraphs with forbidden 4-vertex configurations*. SIAM
  J. Discrete Math. (2010), 946-963.
- [BaTa11] Baber, Rahil and Talbot, John, *Hypergraphs do jump*. Combin. Probab. Comput. (2011),
  161-171.
-/

@[expose] public section

open Asymptotics Filter Topology

namespace Erdos500

/-- `ex₃ n` is $\mathrm{ex}_3(n,K_4^3)$, the largest number of edges of a $3$-uniform hypergraph
on $n$ vertices that contains no $K_4^3$, that is, no set of $4$ vertices that spans all $4$
possible $3$-edges. -/
noncomputable def ex₃ (n : ℕ) : ℕ :=
  sSup {k | ∃ H : Finset (Finset (Fin n)),
    H.IsThreeUniform ∧ ¬ H.ContainsSubgraph 4 4 ∧ H.card = k}

/-- On three vertices the only possible edge is the whole vertex set, so
$\mathrm{ex}_3(3,K_4^3) = 1$. -/
@[category test, AMS 5]
theorem ex₃_three : ex₃ 3 = 1 := by
  have key : ∀ H : Finset (Finset (Fin 3)), H.IsThreeUniform → H.card ≤ 1 := by
    intro H hH
    calc H.card ≤ ({Finset.univ} : Finset (Finset (Fin 3))).card := by
          apply Finset.card_le_card
          intro e he
          rw [Finset.mem_singleton]
          exact Finset.eq_univ_of_card e (by rw [hH e he, Fintype.card_fin])
      _ = 1 := Finset.card_singleton _
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · refine ⟨0, ∅, ?_, ?_, rfl⟩
      · intro e he
        simp at he
      · rintro ⟨S, -, hS⟩
        simp at hS
    · rintro k ⟨H, hH, -, rfl⟩
      exact key H hH
  · refine le_csSup ⟨1, ?_⟩ ⟨{Finset.univ}, ?_, ?_, Finset.card_singleton _⟩
    · rintro k ⟨H, hH, -, rfl⟩
      exact key H hH
    · intro e he
      rw [Finset.mem_singleton] at he
      subst he
      simp
    · rintro ⟨S, hS, -⟩
      have := Finset.card_le_univ S
      rw [Fintype.card_fin] at this
      omega

/-- On four vertices a $K_4^3$ is the set of all four $3$-edges, so $\mathrm{ex}_3(4,K_4^3) = 3$.
Unlike the case $n = 3$, this case depends on the condition `¬ H.ContainsSubgraph 4 4`. -/
@[category test, AMS 5]
theorem ex₃_four : ex₃ 4 = 3 := by
  have key : ∀ H : Finset (Finset (Fin 4)), H.IsThreeUniform → ¬ H.ContainsSubgraph 4 4 →
      H.card ≤ 3 := by
    intro H hH hno
    by_contra hlt
    have hlt : 4 ≤ H.card := by omega
    have hsub : H ⊆ (Finset.univ : Finset (Fin 4)).powersetCard 3 := by
      intro e he
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hH e he⟩
    have hcard : ((Finset.univ : Finset (Fin 4)).powersetCard 3).card = 4 := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      rfl
    have h4 : H.card = 4 := by
      have := Finset.card_le_card hsub
      omega
    apply hno
    refine ⟨Finset.univ, by simp, ?_⟩
    rw [Finset.filter_true_of_mem (fun e _ => Finset.subset_univ e), h4]
  let H0 : Finset (Finset (Fin 4)) := {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}}
  have hH0 : H0.IsThreeUniform := by
    intro e he
    simp only [H0, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> rfl
  have hH0c : H0.card = 3 :=
    Finset.card_eq_three.mpr
      ⟨{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, by decide, by decide, by decide, rfl⟩
  have hH0n : ¬ H0.ContainsSubgraph 4 4 := by
    rintro ⟨S, -, hS⟩
    have := Finset.card_filter_le H0 (fun e => e ⊆ S)
    omega
  apply le_antisymm
  · refine csSup_le ⟨3, H0, hH0, hH0n, hH0c⟩ ?_
    rintro k ⟨H, hH, hno, rfl⟩
    exact key H hH hno
  · refine le_csSup ⟨3, ?_⟩ ⟨H0, hH0, hH0n, hH0c⟩
    rintro k ⟨H, hH, hno, rfl⟩
    exact key H hH hno

/--
What is $\mathrm{ex}_3(n,K_4^3)$? That is, the largest number of $3$-edges which can placed on $n$
vertices so that there exists no $K_4^3$, a set of 4 vertices which is covered by all 4 possible
$3$-edges.

See also [712](https://www.erdosproblems.com/712) for the general case.
-/
@[category research open, AMS 5]
theorem erdos_500 : ∀ n : ℕ, ex₃ n = (answer(sorry) : ℕ → ℕ) n := by
  sorry

/--
A problem of Turán. Turán observed that dividing the vertices into three equal parts
$X_1,X_2,X_3$, and taking the edges to be those triples that either have exactly one vertex in
each part or two vertices in $X_i$ and one vertex in $X_{i+1}$ (where $X_4=X_1$) shows that
$$\mathrm{ex}_3(n,K_4^3)\geq\left(\frac{5}{9}+o(1)\right)\binom{n}{3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_500.variants.lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ ex₃ n := by
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
    (fun n ↦ (ex₃ n : ℝ)) ~[atTop] fun n ↦ 5 / 9 * (n.choose 3 : ℝ) := by
  sorry

/--
The current best upper bound is
$$\mathrm{ex}_3(n,K_4^3)\leq (0.561666+o(1))\binom{n}{3},$$
due to Razborov [Ra10]. (erdosproblems.com gives $0.5611666$ and omits the $o(1)$; without it
the bound fails at $n=4$, where $\mathrm{ex}_3(4,K_4^3)=3>0.561666\binom{4}{3}$.)

[Ra10, (2)] gives this bound in complementary form, as a result that numerical computations
suggest, not as a theorem. [BaTa11] reproduce the computation.
-/
@[category research open, AMS 5]
theorem erdos_500.variants.upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (ex₃ n : ℝ) ≤ (0.561666 + ε) * (n.choose 3 : ℝ) := by
  sorry

/--
The asymptotic form of the question: what is the Turán density
$$\pi(K_4^3)=\lim_{n\to\infty}\frac{\mathrm{ex}_3(n,K_4^3)}{\binom{n}{3}}?$$
By `erdos_500.variants.lower_bound`, $\pi(K_4^3)\geq\frac{5}{9}$.
Turán's conjecture says that $\pi(K_4^3)=\frac{5}{9}$.
-/
@[category research open, AMS 5]
theorem erdos_500.variants.asymptotic :
    Tendsto (fun n : ℕ ↦ (ex₃ n : ℝ) / (n.choose 3 : ℝ)) atTop (𝓝 answer(sorry)) := by
  sorry

end Erdos500
