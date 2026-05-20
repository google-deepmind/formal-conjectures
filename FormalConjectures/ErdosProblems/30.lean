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
addition. Let $h(N)$ denote the maximum size of a Sidon set contained in
$\{1,\dots,N\}$. The Erdős–Turán question (this problem) asks for the
asymptotic refinement $h(N) = \sqrt N + O_\varepsilon(N^\varepsilon)$ for
every $\varepsilon > 0$. That refinement is *open*. Variant theorems in this
file record the classical bounds (Lindström, Erdős–Turán counting,
Balogh–Füredi–Roy, Singer) that frame the conjecture; their per-theorem
docstrings carry the references and page numbers.

### Indexing convention

The canonical statement uses $\{1,\dots,N\}$. The variant theorems below use
$A \subseteq \{0,\dots,N\}$ (i.e. `Finset.range (N+1)`) as a
diameter-normalised form, in which the elementary counting and difference
arguments are cleanest. Translation by $1$ preserves the Sidon property and
cardinality, so $\{0,\dots,N\}$ and $\{1,\dots,N+1\}$ differ only by
normalisation; for each variant, $N$ denotes the maximum element bound.

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
- Mendoza, K. A. (2026). *Sharper Sidon upper bound via residue-class
  pigeonhole.* Sorted-enumeration + telescoping proof of the Lindström
  $\sqrt N + N^{1/4} + 1$ form (~1000 lines of Lean), archived at
  `github.com/MendozaLab/erdos-experiments/tree/main/Erdos30`,
  DOI [`10.5281/zenodo.19444428`](https://doi.org/10.5281/zenodo.19444428).

### AI disclosure

Lean 4 code in this file was drafted with AI assistance. The mathematical
content, Singer/Lindström/Balogh–Füredi–Roy formalizations, and external
archive references are the contributor's responsibility.
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

/- ## Variant 1: Elementary upper bound k(k-1) ≤ 2N

For a Sidon set A ⊆ {0,...,N}, the |A|(|A|-1) ordered pairs (a,b) with a ≠ b
yield distinct positive differences in {1,...,N}, giving |A|(|A|-1)/2 ≤ N. -/

/-- In a Sidon set, distinct pairwise differences identify their endpoints. -/
@[category test, AMS 11]
private lemma sidon_diff_injective (A : Finset ℕ)
    (hS : Finset.IsSidonOrdered A)
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
$|A|(|A|-1) \le 2N$. Hence $|A| \le \sqrt{2N} + O(1)$.

**Reference:** Erdős, P., Turán, P. (1941). *On a problem of Sidon in additive
number theory, and on some related problems.* J. London Math. Soc. **16**,
212–215 (counting argument, p. 212). -/
@[category textbook, AMS 11]
theorem erdos_30.variants.elementary_difference_count (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon ((A : Set ℕ)))
    (hA : A ⊆ Finset.range (N + 1)) :
    A.card * (A.card - 1) ≤ 2 * N := by
  rw [Finset.isSidon_iff_isSidonOrdered] at hS
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

/-- For a Sidon set, $|\text{distinctSums}(A)| = |A|(|A|+1)/2$.

**Reference:** Erdős, P., Turán, P. (1941). *On a problem of Sidon in additive
number theory, and on some related problems.* J. London Math. Soc. **16**,
212–215 (distinct-sums multiset argument, p. 212). -/
@[category textbook, AMS 11]
theorem erdos_30.variants.distinct_sums_card (A : Finset ℕ)
    (hS : IsSidon ((A : Set ℕ))) :
    (distinctSums A).card = A.card * (A.card + 1) / 2 := by
  rw [Finset.isSidon_iff_isSidonOrdered] at hS
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

/-- If $A \subseteq \{0,\dots,N\}$, the distinct Sidon sums lie in $\{0,\dots,2N\}$.

**Reference:** Erdős, P., Turán, P. (1941). *On a problem of Sidon in additive
number theory, and on some related problems.* J. London Math. Soc. **16**,
212–215 (range-containment step, p. 212). -/
@[category textbook, AMS 11]
theorem erdos_30.variants.distinct_sums_in_range (A : Finset ℕ) (N : ℕ)
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
$|A|(|A|+1)/2 \le 2N+1$.

**Reference:** Erdős, P., Turán, P. (1941). *On a problem of Sidon in additive
number theory, and on some related problems.* J. London Math. Soc. **16**,
212–215 (Theorem on p. 213). -/
@[category research solved, AMS 11]
theorem erdos_30.variants.erdos_turan (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon ((A : Set ℕ))) (hA : A ⊆ Finset.range (N + 1)) :
    A.card * (A.card + 1) / 2 ≤ 2 * N + 1 := by
  rw [← erdos_30.variants.distinct_sums_card A hS]
  simpa using Finset.card_le_card (erdos_30.variants.distinct_sums_in_range A N hA)

/- ## Variant 3: Balogh–Füredi–Roy 2023 upper bound

The current best upper bound is h(N) ≤ √N + 0.998·N^{1/4} + 1 for N ≥ 10^12
(Balogh–Füredi–Roy 2023, Amer. Math. Monthly 130(5), arXiv:2103.15850). The
proof combines Erdős–Turán counting (Variant 2) with Lindström's residue-class
inequality (archived externally) via Cauchy–Schwarz.

We record the numerical core of the BFR theorem as a named `Prop`-valued
hypothesis and derive the headline |A| bound from it. -/

/-- Cauchy–Schwarz variance decomposition (BFR Lemma 4.1, real-valued form).

**Reference:** Balogh, J., Füredi, Z., Roy, S. (2023). *An upper bound on the
size of Sidon sets.* Amer. Math. Monthly **130**(5), 437–445, §4 (Lemma 4.1).
arXiv:2103.15850. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.bfr_cauchy_schwarz {v : ℕ} (y : Fin v → ℝ) (d : ℝ) (X : Finset (Fin v))
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
$N \ge 10^{12}$, $|A| \le \sqrt N + 0.998\,N^{1/4} + 1$ (integer form).

**Reference:** Balogh, J., Füredi, Z., Roy, S. (2023). *An upper bound on the
size of Sidon sets.* Amer. Math. Monthly **130**(5), 437–445, Theorem 1 (the
headline bound, p. 437). arXiv:2103.15850. -/
@[category research solved, AMS 11]
theorem erdos_30.variants.bfr (h_bfr : BFRCoreBound)
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

This follows from the elementary `erdos_30.variants.elementary_difference_count`
bound $|A|(|A|-1) \le 2N$ via $(|A|-1)^2 \le |A|(|A|-1)$ and `Nat.le_sqrt`.

**Reference:** Lindström, B. (1969). *An inequality for B₂-sequences.*
J. Combin. Theory **6**, 211–212 (whole paper, two pages). -/
@[category research solved, AMS 11]
theorem erdos_30.variants.lindstrom_weak (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon ((A : Set ℕ)))
    (hA : A ⊆ Finset.range (N + 1)) (hk : 1 < A.card) :
    A.card ≤ Nat.sqrt (2 * N) + 1 := by
  have h := erdos_30.variants.elementary_difference_count A N hS hA
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
`native_decide` (each is fully decidable, axiom-free), and record the prime
case of the general construction as a named `Prop`-valued hypothesis with full
reference.

The cyclic notation $\mathbb{Z}_{q^2+q+1}$ in the per-witness docstrings
below names the construction's *origin* in projective geometry. The
predicate verified in each witness is the ordinary natural-number Sidon
predicate `IsSidon : Set ℕ → Prop` applied to the integer set viewed as a
subset of $\{0,\dots,q^2+q\}$, not a Sidon predicate over a finite cyclic
group. -/

/-- The Singer set for $q=2$: $\{0,1,3\}$, the perfect difference set in
$\mathbb{Z}_7$ arising from the Fano plane.

**Reference:** Concrete witness; the general construction is Singer, J.
(1938), *A theorem in finite projective geometry and some applications to
number theory.* Trans. Amer. Math. Soc. **43**(3), 377–385 (Theorem 1, p. 380). -/
@[category textbook, AMS 11]
theorem erdos_30.variants.singer_q2 :
    IsSidon (({0, 1, 3} : Finset ℕ) : Set ℕ) := by native_decide

/-- The Singer set for $q=3$: $\{0,1,3,9\}$ in $\mathbb{Z}_{13}$.

**Reference:** Concrete witness; general construction in Singer (1938),
Trans. Amer. Math. Soc. **43**(3), Theorem 1, p. 380. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.singer_q3 :
    IsSidon (({0, 1, 3, 9} : Finset ℕ) : Set ℕ) := by native_decide

/-- The Singer set for $q=5$: $\{0,1,3,8,12,18\}$ in $\mathbb{Z}_{31}$.

**Reference:** Concrete witness; general construction in Singer (1938),
Trans. Amer. Math. Soc. **43**(3), Theorem 1, p. 380. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.singer_q5 :
    IsSidon (({0, 1, 3, 8, 12, 18} : Finset ℕ) : Set ℕ) := by native_decide

/-- The Singer set for $q=7$: $\{0,1,3,13,32,36,43,52\}$ in $\mathbb{Z}_{57}$.

**Reference:** Concrete witness; general construction in Singer (1938),
Trans. Amer. Math. Soc. **43**(3), Theorem 1, p. 380. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.singer_q7 :
    IsSidon (({0, 1, 3, 13, 32, 36, 43, 52} : Finset ℕ) : Set ℕ) := by native_decide

/-- The Singer set for $q=11$:
$\{0,1,3,12,20,34,38,81,88,94,104,109\}$ in $\mathbb{Z}_{133}$.

**Reference:** Concrete witness; general construction in Singer (1938),
Trans. Amer. Math. Soc. **43**(3), Theorem 1, p. 380. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.singer_q11 :
    IsSidon (({0, 1, 3, 12, 20, 34, 38, 81, 88, 94, 104, 109} : Finset ℕ) : Set ℕ) := by
  native_decide

/-- The Singer set for $q=13$:
$\{0,1,3,16,23,28,42,76,82,86,119,137,154,175\}$ in $\mathbb{Z}_{183}$.

**Reference:** Concrete witness; general construction in Singer (1938),
Trans. Amer. Math. Soc. **43**(3), Theorem 1, p. 380. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.singer_q13 :
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
hypothesis: for prime $q$, $h(q^2+q) \ge q+1$ via Singer's construction.

**Reference:** Singer, J. (1938). *A theorem in finite projective geometry
and some applications to number theory.* Trans. Amer. Math. Soc. **43**(3),
377–385 (Theorem 1, p. 380). -/
@[category research solved, AMS 11]
theorem erdos_30.variants.singer (h_singer : SingerSidonExists)
    (q : ℕ) (hq : Nat.Prime q) :
    ∃ A : Finset ℕ, IsSidon ((A : Set ℕ)) ∧ A.card = q + 1 ∧
      A ⊆ Finset.range (q * q + q + 1) := by
  obtain ⟨A, hSidon, hCard, hRange⟩ := h_singer q hq
  exact ⟨A, hSidon, hCard,
    fun a ha => Finset.mem_range.mpr (by linarith [hRange a ha])⟩

/-- The Singer bound exceeds $\sqrt N$: $(q+1)^2 > q^2+q$.

**Reference:** Singer (1938), Trans. Amer. Math. Soc. **43**(3), p. 380
(comparison of $q+1$ against $\sqrt{q^2+q}$, i.e. the Sidon-lower-bound
matches $\sqrt N$ to leading order). -/
@[category research solved, AMS 11]
theorem erdos_30.variants.singer_exceeds_sqrt (q : ℕ) (_hq : 0 < q) :
    (q + 1) * (q + 1) > q * q + q := by nlinarith

-- TODO(firsching): add the various known bounds as variants.
end Erdos30
