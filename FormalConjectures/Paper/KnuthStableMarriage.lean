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
# Knuth's extremal conjectures for stable marriage

*Reference:* D. E. Knuth,
[An Exact Analysis of Stable Allocation](https://doi.org/10.1006/jagm.1996.0020),
*Journal of Algorithms* 20 (1996), 431–442, Section 6, p. 441.
The [preprint](https://arxiv.org/pdf/math/9503235#page=8) has the conjectures in Section 6.

Men have independent uniformly random complete strict rankings. Women's rankings are fixed.
The expected proposal count equals the expected sum of men's one-based assigned ranks.
-/

@[expose] public section

namespace KnuthStableMarriage

/-- A fixed profile of women's rankings of men. -/
abbrev Priorities (n : ℕ) := Fin n → Equiv.Perm (Fin n)

/-- Expected number of proposals, averaging over the independent uniform rankings of all men. -/
noncomputable def expectedProposals {n : ℕ} (Q : Priorities n) : ℝ :=
  (∑ P : Priorities n, (StableMarriage.numProposals ⟨P, Q⟩ : ℝ)) /
    Fintype.card (Priorities n)

/-- Woman $j$ ranks men in the order $j,j+1,\ldots,j+n-1$ modulo $n$. -/
def cyclicPriorities (n : ℕ) : Priorities n :=
  fun j ↦ (finCycle j).symm

/-- A profile is cyclic if relabeling both sides gives the cyclic preference lists. -/
def IsCyclic {n : ℕ} (Q : Priorities n) : Prop :=
  ∃ men women : Equiv.Perm (Fin n), ∀ j k, Q (women j) (men (finCycle j k)) = k

/-- With two men, every profile of women's priorities gives expected proposal count $5/2$. -/
@[category test, AMS 5 60 91]
theorem expectedProposals_two (Q : Priorities 2) : expectedProposals Q = 5 / 2 := by
  unfold expectedProposals
  rw [← Nat.cast_sum, StableMarriage.proposal_sum_two Q]
  norm_num [Fintype.card_fun, Fintype.card_perm]

/-- Identical women's priorities are not cyclic at size two. -/
@[category test, AMS 5 60 91]
theorem not_isCyclic_identical_two : ¬ IsCyclic (fun _ ↦ Equiv.refl (Fin 2)) := by
  unfold IsCyclic
  decide

/--
Knuth asks whether the expected number of proposals is always at least $(n+1)H_n-n$.
The lower bound is attained when all women have the same ranking of men.
-/
@[category research open, question, AMS 5 60 91]
theorem minimum_proposals (n : ℕ) (hn : 1 ≤ n) (Q : Priorities n) :
    (n + 1 : ℝ) * (harmonic n : ℝ) - n ≤ expectedProposals Q := by
  sorry

/-- Knuth conjectures that cyclic women's rankings maximize the expected proposal count. -/
@[category research open, AMS 5 60 91]
theorem maximum_proposals (n : ℕ) (hn : 1 ≤ n) (Q : Priorities n) :
    expectedProposals Q ≤ expectedProposals (cyclicPriorities n) := by
  sorry

/--
The uniqueness part of Knuth's cyclic-maximizer conjecture, restricted to $n \ge 3$.
For $n=2$, every priority profile has the same expected proposal count, including noncyclic ones.
-/
@[category research open, AMS 5 60 91]
theorem cyclic_maximizers (n : ℕ) (hn : 3 ≤ n) (Q : Priorities n) :
    (∀ R : Priorities n, expectedProposals R ≤ expectedProposals Q) ↔ IsCyclic Q := by
  sorry

end KnuthStableMarriage
