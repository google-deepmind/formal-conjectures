/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 30

*References:*
- [erdosproblems.com/30](https://www.erdosproblems.com/30)
- [ErTu41] Erdős, P. and Turán, P., *On a problem of Sidon in additive number theory, and on
  some related problems*. J. London Math. Soc. 16 (1941), 212-215.
- [Li69] Lindström, B., *An inequality for $B_2$-sequences*. J. Combinatorial Theory 6 (1969),
  211-212.
- [Si38] Singer, J., *A theorem in finite projective geometry and some applications to number
  theory*. Trans. Amer. Math. Soc. 43 (1938), 377-385.
- [BFR23] Balogh, J., Füredi, Z. and Roy, S., *An upper bound on the size of Sidon sets*.
  Amer. Math. Monthly 130 (2023), 437-445.
- [OB22] O'Bryant, K., *On the size of finite Sidon sets*.
  [arXiv:2207.07800](https://arxiv.org/abs/2207.07800) (2022).
- [CHO25] Carter, D., Hunter, Z. and O'Bryant, K., *On the diameter of finite Sidon sets*.
  Acta Math. Hungar. 175 (2025), 108-126.

See also [Ben Green's Open Problem 31](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf)
(formalised in `FormalConjectures/GreensOpenProblems/31.lean`).
-/

@[expose] public section

namespace Erdos30

/--
Let $h(N)$ be the maximum size of a Sidon set in $\{1, \dots, N\}$.
-/
noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)


open Filter
open scoped Asymptotics Pointwise

/--
Is it true that, for every $\varepsilon > 0$, $h(N) = \sqrt N + O_{\varepsilon}(N^\varepsilon)$
-/
@[category research open, AMS 11]
theorem erdos_30 : answer(sorry) ↔
    ∀ᵉ (ε > 0), (fun N => h N - (N : Real).sqrt) =O[atTop] fun N => (N : ℝ)^(ε : ℝ) := by
  sorry

/--
A stronger conjecture: is it true that $h(N) = \sqrt N + O(1)$?
Erdős thought this was perhaps too optimistic.
-/
@[category research open, AMS 11]
theorem erdos_30.variants.O_one : answer(sorry) ↔
    (fun N => h N - (N : ℝ).sqrt) =O[atTop] fun _ => (1 : ℝ) := by
  sorry

/--
Erdős and Turán [ErTu41] proved $h(N) \le \sqrt N + O(N^{1/4})$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.erdos_turan :
    (fun N => h N - (N : ℝ).sqrt) =O[atTop] fun N => (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

/--
The proofs of Erdős–Turán [ErTu41] and Lindström [Li69] in fact give, for all $N$,
$h(N) \le N^{1/2} + N^{1/4} + 1$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.lindstrom (N : ℕ) :
    (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  sorry

/--
Balogh, Füredi and Roy [BFR23] proved $h(N) \le N^{1/2} + 0.998 N^{1/4}$ for all sufficiently
large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.balogh_furedi_roy :
    ∀ᶠ N in atTop, (h N : ℝ) ≤ (N : ℝ).sqrt + (0.998 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

/--
O'Bryant [OB22] proved $h(N) \le N^{1/2} + 0.99703 N^{1/4}$ for all sufficiently large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.obryant :
    ∀ᶠ N in atTop, (h N : ℝ) ≤ (N : ℝ).sqrt + (0.99703 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

/--
Carter, Hunter and O'Bryant [CHO25] proved $h(N) \le N^{1/2} + 0.98183 N^{1/4} + O(1)$.
This is the current record upper bound.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.carter_hunter_obryant :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      (h N : ℝ) ≤ (N : ℝ).sqrt + (0.98183 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) + C := by
  sorry

/--
Singer's construction [Si38] shows $h(N) \ge (1 - o(1)) N^{1/2}$ for all $N$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.singer :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, (1 - ε) * (N : ℝ).sqrt ≤ h N := by
  sorry

/--
Combining Singer's lower bound [Si38] with the Erdős–Turán upper bound [ErTu41]:
$h(N) \sim N^{1/2}$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.isEquivalent_sqrt :
    (fun N => (h N : ℝ)) ~[atTop] fun N => (N : ℝ).sqrt := by
  sorry

/--
The counting argument of Erdős and Turán [ErTu41]: a Sidon set $A \subseteq \{0, \dots, N\}$
has $|A|(|A| - 1) \le 2N$, because the $|A|(|A|-1)/2$ positive differences of $A$ are distinct
and lie in $\{1, \dots, N\}$.
-/
@[category textbook, AMS 11]
theorem erdos_30.variants.elementary_difference_count (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    A.card * (A.card - 1) ≤ 2 * N := by
  have h_inj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 - p.2)
      (({p ∈ A ×ˢ A | p.2 < p.1} : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    have := Finset.sidon_diff_injective hS h₁.1.1 h₁.1.2 h₂.1.1 h₂.1.2 h₁.2 h₂.2 heq
    exact Prod.ext this.1 this.2
  have h_sub : {p ∈ A ×ˢ A | p.2 < p.1}.image (fun p : ℕ × ℕ ↦ p.1 - p.2) ⊆ Finset.Icc 1 N := by
    simp only [Finset.image_subset_iff, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      and_imp, Prod.forall]
    intro a b ha _ hlt
    have := Finset.mem_range.mp (hA ha)
    lia
  have := Finset.card_le_card h_sub
  rw [Finset.card_image_of_injOn h_inj, Nat.card_Icc] at this
  have := Finset.two_mul_card_product_filter_gt A
  lia

/-- For a Sidon set $A$, $|A + A| = |A|(|A|+1)/2$: the sums $a + b$ with $a \le b$ are pairwise
distinct [ErTu41]. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.distinct_sums_card (A : Finset ℕ) (hS : IsSidon (A : Set ℕ)) :
    (A + A).card = A.card * (A.card + 1) / 2 := by
  rw [Set.isSidon_iff_le] at hS
  have hAA : A + A = {p ∈ A ×ˢ A | p.1 ≤ p.2}.image (fun p ↦ p.1 + p.2) := by
    ext x
    simp only [Finset.mem_add, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      rcases le_total a b with hab | hba
      · exact ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩
      · exact ⟨b, a, ⟨⟨hb, ha⟩, hba⟩, add_comm b a⟩
    · rintro ⟨a, b, ⟨⟨ha, hb⟩, _⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have h_inj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 + p.2)
      (({p ∈ A ×ˢ A | p.1 ≤ p.2} : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    have := hS a₁ h₁.1.1 b₁ h₁.1.2 a₂ h₂.1.1 b₂ h₂.1.2 h₁.2 h₂.2 heq
    exact Prod.ext this.1 this.2
  have h_split : {p ∈ A ×ˢ A | p.1 ≤ p.2} = {p ∈ A ×ˢ A | p.1 < p.2} ∪ A.diag := by
    rw [Finset.diag_eq_filter]
    simp [le_iff_lt_or_eq, Finset.filter_or]
  have h_disj : Disjoint {p ∈ A ×ˢ A | p.1 < p.2} A.diag := by
    rw [Finset.diag_eq_filter]
    exact Finset.disjoint_filter.2 fun _ _ h₁ h₂ ↦ absurd h₂ h₁.ne
  have h_tri := Finset.two_mul_card_product_filter_lt A
  have h_le : A.card ≤ A.card * A.card := Nat.le_mul_self _
  rw [Nat.mul_sub_one] at h_tri
  rw [hAA, Finset.card_image_of_injOn h_inj, h_split, Finset.card_union_of_disjoint h_disj,
    Finset.diag_card, mul_add_one]
  lia

/-- If $A \subseteq \{0, \dots, N\}$ then $A + A \subseteq \{0, \dots, 2N\}$. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.distinct_sums_in_range (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) :
    A + A ⊆ Finset.range (2 * N + 1) := by
  grw [hA, Finset.range_add_range]
  simp [two_mul]

/--
The counting bound of Erdős and Turán [ErTu41] in its sum form: a Sidon set
$A \subseteq \{0, \dots, N\}$ has $|A|(|A| + 1)/2 \le 2N + 1$.
-/
@[category textbook, AMS 11]
theorem erdos_30.variants.erdos_turan_counting (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    A.card * (A.card + 1) / 2 ≤ 2 * N + 1 := by
  rw [← erdos_30.variants.distinct_sums_card A hS]
  simpa using Finset.card_le_card (erdos_30.variants.distinct_sums_in_range A N hA)

/--
A weak form of Lindström's bound [Li69], following from
`erdos_30.variants.elementary_difference_count`: a Sidon set $A \subseteq \{0, \dots, N\}$
has $|A| \le \lfloor \sqrt{2N} \rfloor + 1$.
-/
@[category textbook, AMS 11]
theorem erdos_30.variants.lindstrom_weak (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    A.card ≤ Nat.sqrt (2 * N) + 1 := by
  have h := erdos_30.variants.elementary_difference_count A N hS hA
  have : (A.card - 1) * (A.card - 1) ≤ 2 * N := (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans h
  have := Nat.le_sqrt.mpr this
  lia

end Erdos30
