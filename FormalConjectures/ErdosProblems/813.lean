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
# Erdős Problem 813

*References:*
- [erdosproblems.com/813](https://www.erdosproblems.com/813)
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [BuSu23] Bucić, M. and Sudakov, B., *Large independent sets from local considerations*.
  Combinatorica 43 (2023), 505-546. [arXiv:2007.03667](https://arxiv.org/abs/2007.03667)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos813

/--
Every set of $7$ vertices of `G` contains a triangle, that is, three pairwise adjacent
vertices. For $n < 7$ there is no such set, so the condition is vacuous.
-/
def EverySevenHasTriangle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), S.card = 7 → ∃ t ⊆ S, G.IsNClique 3 t

/--
`h n` is $h(n)$: the smallest clique number of a graph on $n$ vertices in which every set of
$7$ vertices contains a triangle. The complete graph satisfies the condition, so the set is
never empty and `sInf` is a true minimum.
-/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ G : SimpleGraph (Fin n), EverySevenHasTriangle G ∧ G.cliqueNum = k}

/-- The complete graph on $n$ vertices satisfies the condition. -/
@[category test, AMS 5]
theorem everySevenHasTriangle_top (n : ℕ) :
    EverySevenHasTriangle (⊤ : SimpleGraph (Fin n)) := by
  intro S hS
  obtain ⟨t, htS, ht⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
  exact ⟨t, htS, ⟨(SimpleGraph.isClique_univ.2 rfl).subset (Set.subset_univ _), ht⟩⟩

/-- For $n = 7$ the graph must contain a triangle, and a triangle plus $4$ isolated vertices
has clique number $3$, so $h(7) = 3$. -/
@[category test, AMS 5]
theorem h_seven : h 7 = 3 := by
  sorry

/--
Let $h(n)$ be minimal such that every graph on $n$ vertices where every set of $7$ vertices
contains a triangle must contain a clique on at least $h(n)$ vertices. Estimate $h(n)$. In
particular, do there exist constants $c_1, c_2 > 0$ such that
$$n^{1/3+c_1} \ll h(n) \ll n^{1/2-c_2}?$$

The lower half has a positive answer (`Erdos813.erdos_813.variants.lower`); the upper half is
`Erdos813.erdos_813.variants.upper`.
-/
@[category research open, AMS 5]
theorem erdos_813 : answer(sorry) ↔
    ∃ c₁ > (0 : ℝ), ∃ c₂ > (0 : ℝ),
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 + c₁ : ℝ)) =O[atTop] (fun n ↦ (h n : ℝ)) ∧
        (fun n : ℕ ↦ (h n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 - c₂ : ℝ)) := by
  sorry

/--
Erdős and Hajnal proved (see [Er91]) that
$$n^{1/3} \ll h(n) \ll n^{1/2}.$$
-/
@[category research solved, AMS 5]
theorem erdos_813.variants.erdos_hajnal :
    (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ)) =O[atTop] (fun n ↦ (h n : ℝ)) ∧
      (fun n : ℕ ↦ (h n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ)) := by
  sorry

/--
Bucić and Sudakov [BuSu23] proved that $h(n) \gg n^{5/12-o(1)}$. Their result is stated for
graphs in which every $7$ vertices contain an independent set of size $3$; it applies to $h$
by taking complements.
-/
@[category research solved, AMS 5]
theorem erdos_813.variants.bucic_sudakov :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (5 / 12 - ε : ℝ) ≤ (h n : ℝ) := by
  sorry

/--
The lower half of `Erdos813.erdos_813` has a positive answer: there is a constant $c_1 > 0$
with $n^{1/3+c_1} \ll h(n)$. This follows from the bound $h(n) \gg n^{5/12-o(1)}$ of Bucić and
Sudakov [BuSu23], since $5/12 > 1/3$.
-/
@[category research solved, AMS 5]
theorem erdos_813.variants.lower : answer(True) ↔
    ∃ c₁ > (0 : ℝ), (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 + c₁ : ℝ)) =O[atTop] (fun n ↦ (h n : ℝ)) := by
  sorry

/--
The upper half of `Erdos813.erdos_813`: is there a constant $c_2 > 0$ with
$h(n) \ll n^{1/2-c_2}$?
-/
@[category research open, AMS 5]
theorem erdos_813.variants.upper : answer(sorry) ↔
    ∃ c₂ > (0 : ℝ), (fun n : ℕ ↦ (h n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 - c₂ : ℝ)) := by
  sorry

end Erdos813
