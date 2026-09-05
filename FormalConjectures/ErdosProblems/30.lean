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

import FormalConjecturesUtil

/-!
# Erdős Problem 30

*Reference:* [erdosproblems.com/30](https://www.erdosproblems.com/30)

This file records elementary Sidon-set bounds, concrete witnesses, and conditional
consequences of explicitly stated numerical and existence hypotheses. The original
Erdős problem remains open. Each variant's docstring carries its own reference. -/

namespace Erdos30

/--
Let $h(N)$ be the maximum size of a Sidon set in $\{1, \dots, N\}$.
-/
noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)


open Filter
open scoped Pointwise

/--
Is it true that, for every $\varepsilon > 0$, $h(N) = \sqrt N + O_{\varepsilon}(N^\varepsilon)$
-/
@[category research open, AMS 11]
theorem erdos_30 : answer(sorry) ↔
    ∀ᵉ (ε > 0), (fun N => h N - (N : Real).sqrt) =O[atTop] fun N => (N : ℝ)^(ε : ℝ) := by
  sorry

/- ## Variant 1: Elementary upper bound k(k-1) ≤ 2N

For a Sidon set A ⊆ {0,...,N}, the |A|(|A|-1)/2 pairs (a,b) with b < a
yield distinct positive differences in {1,...,N}, giving |A|(|A|-1)/2 ≤ N. -/

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
  -- The difference map `(a, b) ↦ a - b` is injective on the strictly-decreasing pairs of `A`
  -- (Sidon) and lands in `{1, …, N}`, so there are at most `N` such pairs; each unordered
  -- pair of distinct elements gives one, so `|A|(|A|-1) = 2 · (#pairs) ≤ 2N`.
  have h_count := Finset.two_mul_card_product_filter_gt A
  have h_le : ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)).card ≤ N := by
    have h_inj : Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2)
        ↑((A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)) := by
      intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h₁ h₂
      have := Finset.sidon_diff_injective hS h₁.1.1 h₁.1.2 h₂.1.1 h₂.1.2 h₁.2 h₂.2 heq
      exact Prod.ext this.1 this.2
    have h_sub : ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)).image
        (fun p : ℕ × ℕ => p.1 - p.2) ⊆ Finset.Icc 1 N := by
      intro d hd
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hd
      obtain ⟨⟨a, b⟩, ⟨⟨ha, _⟩, hlt⟩, rfl⟩ := hd
      have := Finset.mem_range.mp (hA ha)
      simp only [Finset.mem_Icc]; omega
    have hbound := Finset.card_le_card h_sub
    rw [Finset.card_image_of_injOn h_inj, Nat.card_Icc] at hbound
    omega
  omega

/- ## Variant 2: Distinct pairwise sums (Erdős–Turán counting)

For a Sidon set A of size k, the multiset of sums {a+b : a,b ∈ A, a ≤ b}
has all k(k+1)/2 values distinct. They lie in {2,...,2N}, giving the
Erdős–Turán bound k(k+1)/2 ≤ 2N+1. -/

/-- For a Sidon set, $|(A + A)| = |A|(|A|+1)/2$.

**Reference:** Erdős, P., Turán, P. (1941). *On a problem of Sidon in additive
number theory, and on some related problems.* J. London Math. Soc. **16**,
212–215 (distinct-sums multiset argument, p. 212). -/
@[category textbook, AMS 11]
theorem erdos_30.variants.distinct_sums_card (A : Finset ℕ)
    (hS : IsSidon ((A : Set ℕ))) :
    (A + A).card = A.card * (A.card + 1) / 2 := by
  rw [Finset.isSidon_coe_iff] at hS
  -- $A + A$ is the unordered pairwise-sum set (addition commutes)
  have hAA : A + A =
      ((A ×ˢ A).filter (fun p => p.1 ≤ p.2)).image (fun p => p.1 + p.2) := by
    ext x
    simp only [Finset.mem_add, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      rcases le_total a b with hab | hba
      · exact ⟨(a, b), ⟨⟨ha, hb⟩, hab⟩, rfl⟩
      · exact ⟨(b, a), ⟨⟨hb, ha⟩, hba⟩, add_comm b a⟩
    · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  -- the sum map is injective on the weakly-increasing pairs, so it suffices to count them
  have h_inj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2)
      ↑((A ×ˢ A).filter (fun p => p.1 ≤ p.2)) := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    have := hS a₁ h₁.1.1 b₁ h₁.1.2 a₂ h₂.1.1 b₂ h₂.1.2 h₁.2 h₂.2 heq
    exact Prod.ext this.1 this.2
  rw [hAA, Finset.card_image_of_injOn h_inj]
  -- the weak triangle splits into the strict upper triangle and the diagonal
  have h_split : (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2) =
      (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2) ∪
      (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union]
    constructor
    · intro ⟨⟨ha, hb⟩, hab⟩
      rcases Nat.eq_or_lt_of_le hab with rfl | h
      · exact Or.inr ⟨⟨ha, hb⟩, rfl⟩
      · exact Or.inl ⟨⟨ha, hb⟩, h⟩
    · rintro (⟨⟨ha, hb⟩, h⟩ | ⟨⟨ha, hb⟩, rfl⟩)
      · exact ⟨⟨ha, hb⟩, le_of_lt h⟩
      · exact ⟨⟨ha, hb⟩, le_refl _⟩
  have h_disj : Disjoint ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2))
      ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)) :=
    Finset.disjoint_filter.mpr (fun ⟨_a, _b⟩ _ h1 h2 => absurd h2 (Nat.ne_of_lt h1))
  have h_diag : ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)).card = A.card := by
    rw [← Finset.diag_eq_filter]; exact A.diag_card
  have h_tri := Finset.two_mul_card_product_filter_lt A
  -- relate `|A|(|A|+1)` to the strict-triangle count `|A|(|A|-1)`
  have h_kk1 : A.card * (A.card + 1) = A.card * (A.card - 1) + 2 * A.card := by
    cases A.card with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring
  rw [h_split, Finset.card_union_of_disjoint h_disj, h_diag]
  omega

/-- If $A \subseteq \{0,\dots,N\}$, the distinct Sidon sums lie in $\{0,\dots,2N\}$.

**Reference:** Erdős, P., Turán, P. (1941). *On a problem of Sidon in additive
number theory, and on some related problems.* J. London Math. Soc. **16**,
212–215 (range-containment step, p. 212). -/
@[category textbook, AMS 11]
theorem erdos_30.variants.distinct_sums_in_range (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) :
    A + A ⊆ Finset.range (2 * N + 1) := by
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
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

/- ## Variant 3: Conditional numerical bound

Balogh–Füredi–Roy prove an upper bound with coefficient 0.998 for sufficiently
large intervals. The rounded inequality below is a separate, explicit hypothesis;
no proof or paper-derived threshold for that hypothesis is supplied here. -/

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

/-- An explicit rounded numerical hypothesis for the conditional variant below.

For every Sidon set $A \subseteq \{0,\dots,N\}$ with $N \ge 10^{12}$, assume
$1000(|A|-1) \le 1000\lfloor\sqrt N\rfloor+
998\lfloor\sqrt[4]N\rfloor$.

This definition does not assert the hypothesis. Balogh–Füredi–Roy's theorem
motivates the coefficient 0.998, but does not supply the threshold $10^{12}$
or this rounded inequality.

**Reference for the asymptotic result:** Balogh, J., Füredi, Z., Roy, S. (2023).
*An upper bound on the size of Sidon sets.* Amer. Math. Monthly **130**(5),
437–445, Theorem 1.1. [arXiv:2103.15850](https://arxiv.org/abs/2103.15850). -/
def BFRCoreBound : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ), IsSidon ((A : Set ℕ)) →
    A ⊆ Finset.range (N + 1) → N ≥ 10^12 →
    1000 * (A.card - 1) ≤ 1000 * Nat.sqrt N + 998 * Nat.sqrt (Nat.sqrt N)

/-- A conditional arithmetic consequence of `BFRCoreBound`.

The rounded premise is assumed explicitly; this theorem does not prove the
Balogh–Füredi–Roy asymptotic bound or an explicit threshold for it. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.bfr (h_bfr : BFRCoreBound)
    (A : Finset ℕ) (N : ℕ) (hS : IsSidon ((A : Set ℕ)))
    (hA : A ⊆ Finset.range (N + 1)) (hN : N ≥ 10^12) :
    1000 * A.card ≤ 1000 * Nat.sqrt N + 998 * Nat.sqrt (Nat.sqrt N) + 1000 := by
  have h := h_bfr A N hS hA hN
  omega

/- ## Variant 4: Elementary square-root corollary

Lindström (1969) proved the sharper classical bound
$h(N) < \sqrt N + N^{1/4} + 1$. The following weaker bound follows directly
from counting positive differences. -/

/-- For a Sidon set $A \subseteq \{0,\dots,N\}$ with $|A| \ge 2$,
$|A| \le \lfloor\sqrt{2N}\rfloor + 1$.

This follows from `erdos_30.variants.elementary_difference_count` via
$(|A|-1)^2 \le |A|(|A|-1)$ and `Nat.le_sqrt`.

For the sharper classical bound, see Lindström, B. (1969).
*An inequality for B₂-sequences.* J. Combin. Theory **6**, 211–212. -/
@[category textbook, AMS 11]
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

/- ## Variant 5: Singer 1938 Sidon witnesses

For every prime $q$, projective geometry over $\mathrm{GF}(q)$ yields a Sidon
set of size $q+1$ in $\{0,\dots,q^2+q\}$ (Singer 1938). The points of any line
in $\mathrm{PG}(2,q)$, indexed by a Singer cycle, form a perfect difference
set in $\mathbb{Z}_{q^2+q+1}$, and perfect difference sets are Sidon.

We record concrete witnesses for $q \in \{2,3,5,7,11,13\}$ verified by
`native_decide` on closed decidable propositions, and record the prime
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
suffices for the conditional witness consequence below; the prime-power
case has the same statement form). The full proof uses projective geometry: the
points of a line in $\mathrm{PG}(2,q)$, indexed by powers of a Singer cycle of order
$q^2+q+1$, form a perfect difference set in $\mathbb{Z}_{q^2+q+1}$. Perfect
difference sets are Sidon sets via the difference-injectivity property.

The general construction is assumed here. The concrete cases
$q \in \{2,3,5,7,11,13\}$ above are checked using `native_decide`.

**Reference:** Singer, J. (1938). *A theorem in finite projective geometry
and some applications to number theory.* Trans. Amer. Math. Soc. **43**(3),
377–385. -/
def SingerSidonExists : Prop :=
  ∀ (q : ℕ), Nat.Prime q →
    ∃ A : Finset ℕ, IsSidon ((A : Set ℕ)) ∧ A.card = q + 1 ∧ ∀ a ∈ A, a ≤ q * q + q

/-- **Conditional Singer witness in $\{0,\dots,q^2+q\}$.**
Assuming `SingerSidonExists`, for prime $q$ the conclusion supplies a Sidon
set of size $q+1$ in `Finset.range (q*q+q+1)`. This theorem does not conclude
a bound for `h`, whose defining interval is `Finset.Icc 1 N`.

**Reference:** Singer, J. (1938). *A theorem in finite projective geometry
and some applications to number theory.* Trans. Amer. Math. Soc. **43**(3),
377–385 (Theorem 1, p. 380). -/
@[category textbook, AMS 11]
theorem erdos_30.variants.singer (h_singer : SingerSidonExists)
    (q : ℕ) (hq : Nat.Prime q) :
    ∃ A : Finset ℕ, IsSidon ((A : Set ℕ)) ∧ A.card = q + 1 ∧
      A ⊆ Finset.range (q * q + q + 1) := by
  obtain ⟨A, hSidon, hCard, hRange⟩ := h_singer q hq
  exact ⟨A, hSidon, hCard,
    fun a ha => Finset.mem_range.mpr (by linarith [hRange a ha])⟩

/-- Arithmetic comparison for the Singer parameters: $(q+1)^2 > q^2+q$.
This elementary inequality alone does not assert the existence of a Sidon
set or give a lower bound for `h`. -/
@[category textbook, AMS 11]
theorem erdos_30.variants.singer_exceeds_sqrt (q : ℕ) (_hq : 0 < q) :
    (q + 1) * (q + 1) > q * q + q := by nlinarith

end Erdos30
