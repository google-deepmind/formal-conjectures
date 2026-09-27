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

open Asymptotics Filter

namespace Erdos500

/-- `ex₃ n` is the largest number of edges of a $3$-uniform hypergraph on `n` vertices that
contains no $K_4^3$, that is, no set of $4$ vertices spanning all $4$ possible $3$-edges. -/
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

/--
What is $\mathrm{ex}_3(n,K_4^3)$? That is, the largest number of $3$-edges which can placed on $n$
vertices so that there exists no $K_4^3$, a set of 4 vertices which is covered by all 4 possible
$3$-edges.

See also [712](https://www.erdosproblems.com/712) for the general case.
-/
@[category research open, AMS 5]
theorem erdos_500 (n : ℕ) : ex₃ n = answer(sorry) := by
  sorry

/--
A problem of Turán. Turán observed that dividing the vertices into three equal parts
$X_1,X_2,X_3$, and taking the edges to be those triples that either have exactly one vertex in
each part or two vertices in $X_i$ and one vertex in $X_{i+1}$ (where $X_4=X_1$) shows that
$$\mathrm{ex}_3(n,K_4^3)\geq\left(\frac{5}{9}+o(1)\right)\binom{n}{3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_500.lower_bound (ε : ℝ) (hε : 0 < ε) :
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
theorem erdos_500.variants.turan_conjecture : answer(sorry) ↔
    (fun n ↦ (ex₃ n : ℝ)) ~[atTop] fun n ↦ 5 / 9 * (n.choose 3 : ℝ) := by
  sorry

/--
The current best upper bound is
$$\mathrm{ex}_3(n,K_4^3)\leq 0.5611666\binom{n}{3},$$
due to Razborov [Ra10].

[Ra10] proves the Turán density bound $\pi(K_4^3) \leq 0.561666$, see also
[BaTa11, Section 2.4]. A density bound carries an $o(1)$ term: for example
$\mathrm{ex}_3(4,K_4^3) = 3 > 0.561666 \binom{4}{3}$. The statement formalised here uses the
value of the paper and the $o(1)$ term.
-/
@[category research solved, AMS 5]
theorem erdos_500.upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (ex₃ n : ℝ) ≤ (0.561666 + ε) * (n.choose 3 : ℝ) := by
  sorry

end Erdos500
