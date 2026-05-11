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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 30

*Reference:* [erdosproblems.com/30](https://www.erdosproblems.com/30)

A *Sidon set* (or B₂-set) is a set of natural numbers all of whose pairwise
sums are distinct apart from coincidences forced by the commutativity of
addition. Equivalently, all pairwise differences are distinct. Let $h(N)$
denote the maximum size of a Sidon set contained in $\{1,\dots,N\}$.

The full Erdős–Turán question (this problem) asks for the asymptotic
refinement $h(N) = \sqrt N + O_\varepsilon(N^\varepsilon)$ for every
$\varepsilon > 0$. That refinement is *open*; the prize problem.

This file records the classical bounds that frame the conjecture, plus
small-case witnesses for the lower bound:

* **Elementary upper bound** (counting differences): $h(N)(h(N)-1) \le 2N$.
* **Lindström 1969 weak corollary** (proved here): $|A| \le \lfloor\sqrt{2N}\rfloor + 1$,
  derived from the elementary bound. The sharper $\sqrt N + N^{1/4} + 1$ form
  requires the full sorted-enumeration argument and is archived externally.
* **Erdős–Turán counting** of distinct pairwise sums: a Sidon set of size $k$
  contributes $k(k+1)/2$ distinct sums in $\{2,\dots,2N\}$.
* **Balogh–Füredi–Roy 2023 upper bound** (current best): for $N \ge 10^{12}$,
  $h(N) \le \sqrt N + 0.998\,N^{1/4} + 1$, derived here from a named
  `Prop`-valued hypothesis `BFRCoreBound` (an explicit numerical inequality
  whose full proof requires the combination of Sections 2–4 of the BFR paper).
  The hypothesis is threaded into dependent theorems rather than declared
  as an `axiom`, so consumers must explicitly supply it.
* **Singer 1938 lower bound:** for every prime $q$, $h(q^2+q) \ge q+1$.
  Concretely verified by `native_decide` for $q \in \{2,3,5,7,11,13\}$, with
  the general prime case captured as a named `Prop`-valued hypothesis
  `SingerSidonExists` (full reference below) and threaded into the dependent
  lower-bound theorem rather than declared as an `axiom`.

All variant theorems are stated against the canonical
`FormalConjecturesForMathlib.Combinatorics.IsSidon` predicate. A private
helper `IsSidonSet` (the ordered-pair form) is bridged to `IsSidon` via
`isSidon_iff_isSidonSet` and used internally to reuse counting arguments
that are simpler in the ordered formulation.

### Indexing convention

The original Erdős–Turán problem statement (and `h(N) := Finset.maxSidonSubsetCard
(Finset.Icc 1 N)` above) uses the interval $\{1,\dots,N\}$. The variant
theorems below use $A \subseteq \{0,\dots,N\}$ (i.e. `Finset.range (N+1)`)
as a diameter-normalised form, in which the elementary counting and
difference arguments are cleanest. Translation by $1$ preserves the Sidon
property and cardinality, so $\{0,\dots,N\}$ and $\{1,\dots,N+1\}$ differ
only by normalisation; for each variant, $N$ denotes the maximum element
bound, and the cardinality upper/lower bounds are the same in either
convention.

### References

- Erdős, P., Turán, P. (1941). *On a problem of Sidon in additive number
  theory, and on some related problems.* J. London Math. Soc. **16**, 212–215.
- Lindström, B. (1969). *An inequality for B₂-sequences.*
  J. Combin. Theory **6**, 211–212.
- Singer, J. (1938). *A theorem in finite projective geometry and some
  applications to number theory.* Trans. Amer. Math. Soc. **43** (3), 377–385.
- Balogh, J., Füredi, Z., Roy, S. (2023). *An upper bound on the size of
  Sidon sets.* Amer. Math. Monthly **130** (5), 437–445. arXiv:2103.15850.
- O'Bryant, K. (2004). *A complete annotated bibliography of work related to
  Sidon sets.* Electron. J. Combin., DS11.

### External formal-proof archive

The full proof of the Lindström upper bound (≈1000 lines, residue-class
pigeonhole + sorted-enumeration + telescoping argument) and additional
supporting infrastructure are archived at
`github.com/MendozaLab/erdos-experiments/tree/main/Erdos30`,
DOI [`10.5281/zenodo.19444428`](https://doi.org/10.5281/zenodo.19444428).
-/

namespace Erdos30

/--
Let $h(N)$ be the maximum size of a Sidon set in $\{1, \dots, N\}$.
-/
noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)


open Filter

/--
Is it true that, for every $\varepsilon > 0$, $h(N) = \sqrt N + O_{\varespilon}(N^\varespilon)
-/
@[category research open, AMS 11]
theorem erdos_30 : answer(sorry) ↔
    ∀ᵉ (ε > 0), (fun N => h N - (N : Real).sqrt) =O[atTop] fun N => (N : ℝ)^(ε : ℝ) := by
  sorry

/- ### Internal helper predicate

`IsSidonSet` is an ordered-pair specialisation of `IsSidon` (over `Finset ℕ`),
used internally because several counting arguments below are cleaner stated
with the ordering hypothesis `a_1 ≤ b_1`, `a_2 ≤ b_2` rather than the
up-to-commutativity disjunction. The bridge `isSidon_iff_isSidonSet` shows
the two forms are equivalent. -/

/-- Ordered-pair form of the Sidon predicate, used internally. -/
private abbrev IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ A, ∀ a₂ ∈ A, ∀ b₂ ∈ A,
    a₁ ≤ b₁ → a₂ ≤ b₂ → a₁ + b₁ = a₂ + b₂ → (a₁ = a₂ ∧ b₁ = b₂)

/-- Equivalence of the canonical up-to-commutativity Sidon predicate
(`IsSidon`) and the ordered-pair form (`IsSidonSet`). -/
@[category test, AMS 11]
private lemma isSidon_iff_isSidonSet (A : Finset ℕ) :
    IsSidon ((A : Set ℕ)) ↔ IsSidonSet A := by
  constructor
  · -- IsSidon → IsSidonSet. IsSidon's signature is (i₁, j₁, i₂, j₂) with sum
    -- i₁ + i₂ = j₁ + j₂. We have IsSidonSet's hsum : a₁ + b₁ = a₂ + b₂, so we
    -- map i₁=a₁, j₁=a₂, i₂=b₁, j₂=b₂ to align the sums.
    intro hS a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ hab₁ hab₂ hsum
    have h_mem_a₁ : a₁ ∈ ((A : Set ℕ)) := Finset.mem_coe.mpr ha₁
    have h_mem_b₁ : b₁ ∈ ((A : Set ℕ)) := Finset.mem_coe.mpr hb₁
    have h_mem_a₂ : a₂ ∈ ((A : Set ℕ)) := Finset.mem_coe.mpr ha₂
    have h_mem_b₂ : b₂ ∈ ((A : Set ℕ)) := Finset.mem_coe.mpr hb₂
    have h_disj := hS a₁ h_mem_a₁ a₂ h_mem_a₂ b₁ h_mem_b₁ b₂ h_mem_b₂ hsum
    -- h_disj : (a₁ = a₂ ∧ b₁ = b₂) ∨ (a₁ = b₂ ∧ b₁ = a₂)
    cases h_disj with
    | inl h => exact h
    | inr h =>
      -- Case: a₁ = b₂, b₁ = a₂. With a₁ ≤ b₁ and a₂ ≤ b₂ this forces all four
      -- values equal, so the conclusion still holds.
      obtain ⟨ha, hb⟩ := h
      refine ⟨?_, ?_⟩ <;> omega
  · -- IsSidonSet → IsSidon. Sort each pair to invoke the ordered hypothesis.
    intro hS i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    rw [Finset.mem_coe] at hi₁ hj₁ hi₂ hj₂
    by_cases h₁ : i₁ ≤ i₂
    · by_cases h₂ : j₁ ≤ j₂
      · have := hS i₁ hi₁ i₂ hi₂ j₁ hj₁ j₂ hj₂ h₁ h₂ hsum
        exact Or.inl ⟨this.1, this.2⟩
      · push_neg at h₂
        have h₂' : j₂ ≤ j₁ := Nat.le_of_lt h₂
        have hsum' : i₁ + i₂ = j₂ + j₁ := by omega
        have := hS i₁ hi₁ i₂ hi₂ j₂ hj₂ j₁ hj₁ h₁ h₂' hsum'
        exact Or.inr ⟨this.1, this.2⟩
    · push_neg at h₁
      have h₁' : i₂ ≤ i₁ := Nat.le_of_lt h₁
      by_cases h₂ : j₁ ≤ j₂
      · have hsum' : i₂ + i₁ = j₁ + j₂ := by omega
        have := hS i₂ hi₂ i₁ hi₁ j₁ hj₁ j₂ hj₂ h₁' h₂ hsum'
        exact Or.inr ⟨this.2, this.1⟩
      · push_neg at h₂
        have h₂' : j₂ ≤ j₁ := Nat.le_of_lt h₂
        have hsum' : i₂ + i₁ = j₂ + j₁ := by omega
        have := hS i₂ hi₂ i₁ hi₁ j₂ hj₂ j₁ hj₁ h₁' h₂' hsum'
        exact Or.inl ⟨this.2, this.1⟩

/- ## Variant 1: Elementary upper bound k(k-1) ≤ 2N

For a Sidon set A ⊆ {0,...,N}, the |A|(|A|-1) ordered pairs (a,b) with a ≠ b
yield distinct positive differences in {1,...,N}, giving |A|(|A|-1)/2 ≤ N. -/

/-- In a Sidon set, distinct pairwise differences identify their endpoints. -/
@[category test, AMS 11]
private lemma sidon_diff_injective (A : Finset ℕ)
    (hS : IsSidonSet A)
    (a₁ b₁ a₂ b₂ : ℕ)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (hlt₁ : b₁ < a₁) (hlt₂ : b₂ < a₂)
    (heq : a₁ - b₁ = a₂ - b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have h_sum : a₁ + b₂ = a₂ + b₁ := by omega
  by_cases h1 : b₂ ≤ a₁
  · by_cases h2 : b₁ ≤ a₂
    · have h_sidon := hS b₂ hb₂ a₁ ha₁ b₁ hb₁ a₂ ha₂ h1 h2 (by omega)
      exact ⟨h_sidon.right, h_sidon.left.symm⟩
    · push_neg at h2
      have h_sidon := hS b₂ hb₂ a₁ ha₁ a₂ ha₂ b₁ hb₁ h1 (Nat.le_of_lt h2) (by omega)
      exact absurd h_sidon.right.symm (Nat.ne_of_lt hlt₁)
  · push_neg at h1
    by_cases h2 : b₁ ≤ a₂
    · have h_sidon := hS a₁ ha₁ b₂ hb₂ b₁ hb₁ a₂ ha₂ (Nat.le_of_lt h1) h2 (by omega)
      exact absurd h_sidon.left.symm (Nat.ne_of_lt hlt₁)
    · push_neg at h2
      have h_sidon := hS a₁ ha₁ b₂ hb₂ a₂ ha₂ b₁ hb₁ (Nat.le_of_lt h1)
        (Nat.le_of_lt h2) (by omega)
      exact ⟨h_sidon.left, h_sidon.right.symm⟩

/-- **Elementary upper bound.** For a Sidon set $A \subseteq \{0,\dots,N\}$,
$|A|(|A|-1) \le 2N$. Hence $|A| \le \sqrt{2N} + O(1)$. -/
@[category research solved, AMS 11]
theorem sidon_difference_count (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon ((A : Set ℕ)))
    (hA : A ⊆ Finset.range (N + 1)) :
    A.card * (A.card - 1) ≤ 2 * N := by
  rw [isSidon_iff_isSidonSet] at hS
  set pairs := Finset.filter (fun p : ℕ × ℕ => p.2 < p.1) (A ×ˢ A)
  set diff_map := fun (p : ℕ × ℕ) => p.1 - p.2
  have h_inj : Set.InjOn diff_map (↑pairs) := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    have := sidon_diff_injective A hS a₁ b₁ a₂ b₂ h₁.1.1 h₁.1.2 h₂.1.1 h₂.1.2
      h₁.2 h₂.2 heq
    exact Prod.ext this.1 this.2
  have h_range : Finset.image diff_map pairs ⊆ Finset.Icc 1 N := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := hd
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, _hb⟩, hlt⟩ := hp
    rw [Finset.mem_Icc]
    show 1 ≤ a - b ∧ a - b ≤ N
    refine ⟨by omega, ?_⟩
    have : a ≤ N := by
      have := Finset.mem_range.mp (hA ha); omega
    omega
  have h_card_img : (Finset.image diff_map pairs).card ≤ N := by
    have := Finset.card_le_card h_range
    simp at this
    exact this
  have h_eq_inj : (Finset.image diff_map pairs).card = pairs.card :=
    Finset.card_image_of_injOn h_inj
  have h_pairs : pairs.card = A.card * (A.card - 1) / 2 := by
    have : pairs.card = (Finset.powersetCard 2 A).card := by
      refine Finset.card_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_
      · intro ⟨a, b⟩ hp
        rw [Finset.mem_filter, Finset.mem_product] at hp
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hp.1.1
          · exact hp.1.2
        · exact Finset.card_pair (Nat.ne_of_gt hp.2)
      · intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
        rw [Finset.mem_filter, Finset.mem_product] at h₁ h₂
        have h₁lt := h₁.2
        have _h₂lt := h₂.2
        change ({a₁, b₁} : Finset ℕ) = ({a₂, b₂} : Finset ℕ) at heq
        suffices h : a₁ = a₂ ∧ b₁ = b₂ from Prod.ext h.1 h.2
        have h_a₁_in : a₁ ∈ ({a₂, b₂} : Finset ℕ) := by
          rw [← heq]; exact Finset.mem_insert_self _ _
        have h_b₁_in : b₁ ∈ ({a₂, b₂} : Finset ℕ) := by
          rw [← heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
        simp only [Finset.mem_insert, Finset.mem_singleton] at h_a₁_in h_b₁_in
        rcases h_a₁_in with h_a1_a2 | h_a1_b2
        · rcases h_b₁_in with h_b1_a2 | h_b1_b2
          · omega
          · exact ⟨h_a1_a2, h_b1_b2⟩
        · rcases h_b₁_in with _h_b1_a2 | _h_b1_b2
          · omega
          · omega
      · intro s hs
        rw [Finset.mem_powersetCard] at hs
        obtain ⟨hsub, hcard⟩ := hs
        rw [Finset.card_eq_two] at hcard
        obtain ⟨x, y, hxy, rfl⟩ := hcard
        cases Nat.lt_or_gt_of_ne hxy with
        | inl hlt =>
          refine ⟨(y, x), ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_product]
            refine ⟨⟨?_, ?_⟩, hlt⟩
            · exact hsub (by simp)
            · exact hsub (by simp)
          · change ({y, x} : Finset ℕ) = ({x, y} : Finset ℕ)
            exact Finset.pair_comm y x
        | inr hgt =>
          refine ⟨(x, y), ?_, rfl⟩
          rw [Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨?_, ?_⟩, hgt⟩
          · exact hsub (by simp)
          · exact hsub (by simp)
    rw [this, Finset.card_powersetCard, Nat.choose_two_right]
  have h_div : A.card * (A.card - 1) / 2 ≤ N := by
    rw [← h_pairs, ← h_eq_inj]; exact h_card_img
  have h_even : Even (A.card * (A.card - 1)) := by
    rcases Nat.even_or_odd A.card with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m * (A.card - 1), by rw [hm]; ring⟩
    · refine ⟨A.card * m, ?_⟩
      have : A.card - 1 = 2 * m := by omega
      rw [this, hm]; ring
  obtain ⟨k, hk⟩ := h_even
  rw [hk] at h_div
  rw [hk]
  omega

/- ## Variant 2: Distinct pairwise sums (Erdős–Turán counting)

For a Sidon set A of size k, the multiset of sums {a+b : a,b ∈ A, a ≤ b}
has all k(k+1)/2 values distinct. They lie in {2,...,2N}, giving the
Erdős–Turán bound k(k+1)/2 ≤ 2N+1. -/

/-- The set of distinct pairwise sums $a+b$ with $a \le b$ from $A$. -/
def distinctSums (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≤ p.2)).image (fun p => p.1 + p.2)

/-- For a Sidon set, $|\text{distinctSums}(A)| = |A|(|A|+1)/2$. -/
@[category research solved, AMS 11]
theorem card_distinctSums_sidon (A : Finset ℕ)
    (hS : IsSidon ((A : Set ℕ))) :
    (distinctSums A).card = A.card * (A.card + 1) / 2 := by
  rw [isSidon_iff_isSidonSet] at hS
  have h_inj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2)
      ↑((A ×ˢ A).filter (fun p => p.1 ≤ p.2)) := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    have := hS a₁ h₁.1.1 b₁ h₁.1.2 a₂ h₂.1.1 b₂ h₂.1.2 h₁.2 h₂.2 heq
    exact Prod.ext this.1 this.2
  unfold distinctSums
  rw [Finset.card_image_of_injOn h_inj]
  have h_le_eq : (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2) =
      ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)) ∪
      ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union]
    constructor
    · intro ⟨⟨ha, hb⟩, hab⟩
      rcases Nat.eq_or_lt_of_le hab with rfl | h
      · right; exact ⟨⟨ha, hb⟩, rfl⟩
      · left; exact ⟨⟨ha, hb⟩, h⟩
    · rintro (⟨⟨ha, hb⟩, h⟩ | ⟨⟨ha, hb⟩, rfl⟩)
      · exact ⟨⟨ha, hb⟩, le_of_lt h⟩
      · exact ⟨⟨ha, hb⟩, le_refl _⟩
  have h_le_disj : Disjoint
      ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2))
      ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)) :=
    Finset.disjoint_filter.mpr (fun ⟨_a, _b⟩ _ h1 h2 => absurd h2 (Nat.ne_of_lt h1))
  rw [h_le_eq, Finset.card_union_of_disjoint h_le_disj]
  have h_diag : ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)).card = A.card := by
    rw [← Finset.diag_eq_filter]; exact A.diag_card
  rw [h_diag]
  have h_filter_eq : (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2) =
      A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
    constructor
    · intro ⟨⟨ha, hb⟩, hab⟩; exact ⟨⟨ha, hb, Nat.ne_of_lt hab⟩, hab⟩
    · intro ⟨⟨ha, hb, _⟩, hab⟩; exact ⟨⟨ha, hb⟩, hab⟩
  rw [h_filter_eq]
  have h_union : A.offDiag =
      A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2) ∪
      A.offDiag.filter (fun p : ℕ × ℕ => p.2 < p.1) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ⟨ha, hb, hab⟩
      rcases lt_or_gt_of_ne hab with h | h
      · left; exact ⟨⟨ha, hb, hab⟩, h⟩
      · right; exact ⟨⟨ha, hb, hab⟩, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have h_disj : Disjoint
      (A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2))
      (A.offDiag.filter (fun p : ℕ × ℕ => p.2 < p.1)) :=
    Finset.disjoint_filter.mpr
      (fun ⟨_a, _b⟩ _ h1 h2 => absurd h1 (not_lt.mpr (le_of_lt h2)))
  have h_swap : (A.offDiag.filter (fun p : ℕ × ℕ => p.2 < p.1)).card =
      (A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2)).card :=
    Finset.card_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1))
      (fun ⟨_a, _b⟩ h => by
        simp only [Finset.mem_filter, Finset.mem_offDiag] at h ⊢
        exact ⟨⟨h.1.2.1, h.1.1, Ne.symm h.1.2.2⟩, h.2⟩)
      (fun ⟨_a, _b⟩ h => by
        simp only [Finset.mem_filter, Finset.mem_offDiag] at h ⊢
        exact ⟨⟨h.1.2.1, h.1.1, Ne.symm h.1.2.2⟩, h.2⟩)
      (fun _ _ => rfl) (fun _ _ => rfl)
  have h_card : A.offDiag.card =
      (A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2)).card +
      (A.offDiag.filter (fun p : ℕ × ℕ => p.2 < p.1)).card := by
    rw [← Finset.card_union_of_disjoint h_disj, ← h_union]
  rw [h_swap] at h_card
  have h_mul_sub : A.card * (A.card - 1) = A.card * A.card - A.card := by
    cases A.card with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_sub_one]
      rw [show (n + 1) * (n + 1) = (n + 1) * n + (n + 1) from by ring,
        Nat.add_sub_cancel]
  have h_offDiag_eq : A.offDiag.card = A.card * (A.card - 1) :=
    A.offDiag_card.trans h_mul_sub.symm
  have h_2c : 2 * (A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2)).card =
      A.card * (A.card - 1) := by linarith
  have h_lt_card : (A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2)).card =
      A.card * (A.card - 1) / 2 := by
    have : A.card * (A.card - 1) / 2 =
        (A.offDiag.filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
      rw [← h_2c]; exact Nat.mul_div_cancel_left _ (by omega)
    exact this.symm
  rw [h_lt_card]
  have h_kk1 : A.card * (A.card + 1) = A.card * (A.card - 1) + 2 * A.card := by
    cases A.card with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring
  rw [h_kk1, show 2 * A.card = A.card * 2 from by ring,
    Nat.add_mul_div_right _ _ (by omega : (0:ℕ) < 2)]

/-- If $A \subseteq \{0,\dots,N\}$, the distinct Sidon sums lie in $\{0,\dots,2N\}$. -/
@[category research solved, AMS 11]
theorem distinctSums_subset_range (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) :
    distinctSums A ⊆ Finset.range (2 * N + 1) := by
  intro s hs
  simp only [distinctSums, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hs
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := hs
  have haN : a ≤ N := by
    have := Finset.mem_range.mp (hA ha); omega
  have hbN : b ≤ N := by
    have := Finset.mem_range.mp (hA hb); omega
  exact Finset.mem_range.mpr (by omega)

/-- **Erdős–Turán counting bound.** For a Sidon set $A \subseteq \{0,\dots,N\}$,
$|A|(|A|+1)/2 \le 2N+1$. -/
@[category research solved, AMS 11]
theorem erdos_turan_counting_bound (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon ((A : Set ℕ))) (hA : A ⊆ Finset.range (N + 1)) :
    A.card * (A.card + 1) / 2 ≤ 2 * N + 1 := by
  rw [← card_distinctSums_sidon A hS]
  simpa using Finset.card_le_card (distinctSums_subset_range A N hA)

/- ## Variant 3: Balogh–Füredi–Roy 2023 upper bound

The current best upper bound is h(N) ≤ √N + 0.998·N^{1/4} + 1 for N ≥ 10^12
(Balogh–Füredi–Roy 2023, Amer. Math. Monthly 130(5), arXiv:2103.15850). The
proof combines Erdős–Turán counting (Variant 2) with Lindström's residue-class
inequality (archived externally) via Cauchy–Schwarz.

We axiomatize the numerical core of the BFR theorem and derive the headline
|A| bound from it. -/

/-- Cauchy–Schwarz variance decomposition (BFR Lemma 4.1, real-valued form). -/
@[category research solved, AMS 11]
theorem bfr_cauchy_schwarz {v : ℕ} (y : Fin v → ℝ) (d : ℝ) (X : Finset (Fin v))
    (d_X : ℝ) (hd_X : d_X * X.card = ∑ x ∈ X, y x) :
    ∑ i, (d - y i) ^ 2 ≥
      X.card * (d - d_X) ^ 2 + ∑ x ∈ X, (y x) ^ 2 - X.card * d_X ^ 2 := by
  have h_ge : ∑ x ∈ X, (d - y x) ^ 2 ≤ ∑ i, (d - y i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X)
      (fun _ _ _ => sq_nonneg _)
  suffices h_eq : ∑ x ∈ X, (d - y x) ^ 2 =
      ↑X.card * (d - d_X) ^ 2 + ∑ x ∈ X, (y x) ^ 2 - ↑X.card * d_X ^ 2 by linarith
  have h_congr : ∀ x ∈ X, (d - y x) ^ 2 = d ^ 2 - 2 * d * y x + (y x) ^ 2 :=
    fun _x _ => by ring
  rw [Finset.sum_congr rfl h_congr, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have h_rhs : ↑X.card * (d - d_X) ^ 2 + ∑ x ∈ X, (y x) ^ 2 - ↑X.card * d_X ^ 2 =
      ↑X.card * d ^ 2 - 2 * d * (d_X * ↑X.card) + ∑ x ∈ X, (y x) ^ 2 := by ring
  rw [h_rhs, hd_X]

/-- **Named hypothesis (BFR core, 2023; numerical specialisation).**
Specialised numerical form of the Balogh–Füredi–Roy bound, captured as a
`Prop`-valued definition so consumers must thread it explicitly rather than
inheriting it from an `axiom`. The statement: for every Sidon set
$A \subseteq \{0,\dots,N\}$ with $N \ge 10^{12}$,
$1000 \cdot (|A| - 1) \le 1000 \cdot \lfloor\sqrt N\rfloor +
998 \cdot \lfloor\sqrt[4] N\rfloor$.

**Note on scope.** Balogh–Füredi–Roy (2023) prove their headline bound
$|A| \le \sqrt N + 0.998\,N^{1/4} + 1$ for *sufficiently large* $N$ without
giving an explicit threshold in the paper. The hypothesis recorded here is
a formal numerical specialisation in $\mathbb{N}$-arithmetic — extracted
from the paper's coefficient analysis — using $N \ge 10^{12}$ as a
conservative threshold under which the `Nat.sqrt` rounding losses are
absorbed by the slack between the paper's coefficient $63/64 \approx 0.984$
and the Monthly form $0.998$. This is not a literal restatement of any
single inequality in the paper.

The full proof requires the combination of:
- Section 2: Erdős–Turán discrepancy with slack term $C$ (interval decomposition,
  representation function distribution analysis).
- Section 3: set-systems / residue-class bound $k^2 m \le (2N + m - 1)(m + k - 1)$.
- Section 4: Cauchy–Schwarz combination yielding coefficient $63/64$.

**Reference:** Balogh, J., Füredi, Z., Roy, S. (2023). *An upper bound on the
size of Sidon sets.* Amer. Math. Monthly **130**(5), 437–445. arXiv:2103.15850. -/
def BFRCoreBound : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ), IsSidon ((A : Set ℕ)) →
    A ⊆ Finset.range (N + 1) → N ≥ 10^12 →
    1000 * (A.card - 1) ≤ 1000 * Nat.sqrt N + 998 * Nat.sqrt (Nat.sqrt N)

/-- **Balogh–Füredi–Roy 2023 upper bound.** Conditional on the named
`BFRCoreBound` hypothesis: for a Sidon set $A \subseteq \{0,\dots,N\}$ with
$N \ge 10^{12}$, $|A| \le \sqrt N + 0.998\,N^{1/4} + 1$ (integer form). -/
@[category research solved, AMS 11]
theorem bfr_bound (h_bfr : BFRCoreBound)
    (A : Finset ℕ) (N : ℕ) (hS : IsSidon ((A : Set ℕ)))
    (hA : A ⊆ Finset.range (N + 1)) (hN : N ≥ 10^12) :
    1000 * A.card ≤ 1000 * Nat.sqrt N + 998 * Nat.sqrt (Nat.sqrt N) + 1000 := by
  have h := h_bfr A N hS hA hN
  omega

/- ## Variant 4: Lindström 1969 weak corollary (proved)

Lindström (1969) proved the sharper classical form $h(N) \le \sqrt N + N^{1/4} + 1$.
That sharper bound requires the full sorted-enumeration + telescoping argument
(≈1000 lines of Lean); the machine-checked proof of the sharper form lives in
the external archive (github.com/MendozaLab/erdos-experiments/tree/main/Erdos30,
DOI 10.5281/zenodo.19444428).

The weaker $|A| \le \lfloor\sqrt{2N}\rfloor + 1$ form is an immediate corollary
of the elementary $|A|(|A|-1) \le 2N$ bound proved above, and is recorded here
historically as Lindström's weak form. -/

/-- **Lindström weak form (corollary).** For a Sidon set $A \subseteq \{0,\dots,N\}$
with $N \ge 1$ and $|A| \ge 2$, $|A| \le \lfloor\sqrt{2N}\rfloor + 1$.

This follows from the elementary `sidon_difference_count` bound
$|A|(|A|-1) \le 2N$ via $(|A|-1)^2 \le |A|(|A|-1)$ and `Nat.le_sqrt`.

**Reference:** Lindström, B. (1969). *An inequality for B₂-sequences.*
J. Combin. Theory **6**, 211–212. -/
@[category research solved, AMS 11]
theorem lindstrom_bound_weak (A : Finset ℕ) (N : ℕ) (hS : IsSidon ((A : Set ℕ)))
    (hA : A ⊆ Finset.range (N + 1)) (hk : 1 < A.card) :
    A.card ≤ Nat.sqrt (2 * N) + 1 := by
  have h := sidon_difference_count A N hS hA
  have h_le : A.card - 1 ≤ A.card := Nat.sub_le _ _
  have h_mul : (A.card - 1) * (A.card - 1) ≤ A.card * (A.card - 1) :=
    Nat.mul_le_mul_right _ h_le
  have h_sq : (A.card - 1) * (A.card - 1) ≤ 2 * N := le_trans h_mul h
  have h_sqrt_le : A.card - 1 ≤ Nat.sqrt (2 * N) := Nat.le_sqrt.mpr h_sq
  omega

/- ## Variant 5: Singer 1938 lower bound

For every prime $q$, projective geometry over $\mathrm{GF}(q)$ yields a Sidon
set of size $q+1$ in $\{0,\dots,q^2+q\}$ (Singer 1938). The points of any line
in $\mathrm{PG}(2,q)$, indexed by a Singer cycle, form a perfect difference
set in $\mathbb{Z}_{q^2+q+1}$, and perfect difference sets are Sidon.

We record concrete witnesses for $q \in \{2,3,5,7,11,13\}$ verified by
`native_decide` (each is fully decidable, axiom-free), and axiomatize the
prime case of the general construction with full reference.

The cyclic notation $\mathbb{Z}_{q^2+q+1}$ in the per-witness docstrings
below names the construction's *origin* in projective geometry. The
predicate verified in each witness is the ordinary natural-number Sidon
predicate `IsSidon : Set ℕ → Prop` applied to the integer set viewed as a
subset of $\{0,\dots,q^2+q\}$, not a Sidon predicate over a finite cyclic
group. -/

/-- The Singer set for $q=2$: $\{0,1,3\}$, the perfect difference set in
$\mathbb{Z}_7$ arising from the Fano plane. -/
@[category research solved, AMS 11]
theorem singer_q2_sidon : IsSidon (({0, 1, 3} : Finset ℕ) : Set ℕ) := by native_decide

/-- The Singer set for $q=3$: $\{0,1,3,9\}$ in $\mathbb{Z}_{13}$. -/
@[category research solved, AMS 11]
theorem singer_q3_sidon : IsSidon (({0, 1, 3, 9} : Finset ℕ) : Set ℕ) := by native_decide

/-- The Singer set for $q=5$: $\{0,1,3,8,12,18\}$ in $\mathbb{Z}_{31}$. -/
@[category research solved, AMS 11]
theorem singer_q5_sidon :
    IsSidon (({0, 1, 3, 8, 12, 18} : Finset ℕ) : Set ℕ) := by native_decide

/-- The Singer set for $q=7$: $\{0,1,3,13,32,36,43,52\}$ in $\mathbb{Z}_{57}$. -/
@[category research solved, AMS 11]
theorem singer_q7_sidon :
    IsSidon (({0, 1, 3, 13, 32, 36, 43, 52} : Finset ℕ) : Set ℕ) := by native_decide

/-- The Singer set for $q=11$:
$\{0,1,3,12,20,34,38,81,88,94,104,109\}$ in $\mathbb{Z}_{133}$. -/
@[category research solved, AMS 11]
theorem singer_q11_sidon :
    IsSidon (({0, 1, 3, 12, 20, 34, 38, 81, 88, 94, 104, 109} : Finset ℕ) : Set ℕ) := by
  native_decide

/-- The Singer set for $q=13$:
$\{0,1,3,16,23,28,42,76,82,86,119,137,154,175\}$ in $\mathbb{Z}_{183}$. -/
@[category research solved, AMS 11]
theorem singer_q13_sidon :
    IsSidon
      (({0, 1, 3, 16, 23, 28, 42, 76, 82, 86, 119, 137, 154, 175} : Finset ℕ) : Set ℕ) := by
  native_decide

/-- **Named hypothesis (prime case of Singer's 1938 construction).** For
every prime $q$, there exists a Sidon set of size $q+1$ with all elements
$\le q^2+q$. Captured as a `Prop`-valued definition so consumers must thread
it explicitly rather than inheriting it from an `axiom`.

Singer's original theorem covers every prime *power* $q$. The hypothesis
recorded here is the conservative restriction to the prime case (which
suffices for the lower-bound consequence below; the prime-power case extends
in the same form). The full proof uses projective geometry: the points of a
line in $\mathrm{PG}(2,q)$, indexed by powers of a Singer cycle of order
$q^2+q+1$, form a perfect difference set in $\mathbb{Z}_{q^2+q+1}$. Perfect
difference sets are Sidon sets via the difference-injectivity property.

The general formalization requires `GaloisField` machinery (cyclic structure
of $\mathrm{GF}(q^3)^\times$), trace/norm maps from $\mathrm{GF}(q^3)$ to
$\mathrm{GF}(q)$, and a Singer-cycle construction not currently in Mathlib.
Concrete cases $q \in \{2,3,5,7,11,13\}$ above are fully decidable via
`native_decide`.

**Reference:** Singer, J. (1938). *A theorem in finite projective geometry
and some applications to number theory.* Trans. Amer. Math. Soc. **43**(3),
377–385. -/
def SingerSidonExists : Prop :=
  ∀ (q : ℕ), Nat.Prime q →
    ∃ A : Finset ℕ, IsSidon ((A : Set ℕ)) ∧ A.card = q + 1 ∧ ∀ a ∈ A, a ≤ q * q + q

/-- **Singer lower bound.** Conditional on the named `SingerSidonExists`
hypothesis: for prime $q$, $h(q^2+q) \ge q+1$ via Singer's construction. -/
@[category research solved, AMS 11]
theorem singer_lower_bound (h_singer : SingerSidonExists)
    (q : ℕ) (hq : Nat.Prime q) :
    ∃ A : Finset ℕ, IsSidon ((A : Set ℕ)) ∧ A.card = q + 1 ∧
      A ⊆ Finset.range (q * q + q + 1) := by
  obtain ⟨A, hSidon, hCard, hRange⟩ := h_singer q hq
  exact ⟨A, hSidon, hCard,
    fun a ha => Finset.mem_range.mpr (by linarith [hRange a ha])⟩

/-- The Singer bound exceeds $\sqrt N$: $(q+1)^2 > q^2+q$. -/
@[category research solved, AMS 11]
theorem singer_exceeds_sqrt (q : ℕ) (_hq : 0 < q) :
    (q + 1) * (q + 1) > q * q + q := by nlinarith

-- TODO(firsching): add the various known bounds as variants.
end Erdos30
