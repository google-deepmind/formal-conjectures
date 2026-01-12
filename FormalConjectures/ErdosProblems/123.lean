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
# Erdős Problem 123

*References:*
- [erdosproblems.com/123](https://www.erdosproblems.com/123)
- [ErLe96] Erdős, P. and Lewin, Mordechai, _$d$-complete sequences of integers_. Math. Comp. (1996), 837-840.
- [Er92b] Erdős, Paul, _Some of my favourite problems in various branches of combinatorics_. Matematiche (Catania) (1992), 231-240.
-/

open Filter
open Submonoid
open scoped Pointwise

namespace Erdos123

/--
A set `A` of natural numbers is **d-complete** if every sufficiently large integer
is the sum of distinct elements of `A` such that no element divides another.

Reference: [ErLe96] Erdős, P. and Lewin, M., _$d$-complete sequences of integers_. Math. Comp. (1996).
-/
def IsDComplete (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ A ∧                  -- The summands come from A
    IsAntichain (· ∣ ·) (s : Set ℕ) ∧   -- No summand divides another
    s.sum id = n                        -- They sum to n

/--
Characterizes a "snug" finite set of natural numbers:
all elements are within a multiplicative factor $(1 + ε)$ of the minimum.
Specifically, for a finite set $A$ and $ε > 0$, all $a ∈ A$ satisfy $a < (1 + ε) · min(A)$.
-/
def IsSnug (ε : ℝ) (A : Finset ℕ) : Prop :=
  ∃ hA : A.Nonempty, ∀ a ∈ A, a < (1 + ε) * A.min' hA

/--
Predicate for pairwise coprimality of three integers.
Requires all three input values to be pairwise coprime to each other.
-/
def PairwiseCoprime (a b c : ℕ) : Prop := Pairwise (Nat.Coprime.onFun ![a, b, c])

/--
**Erdős Problem #123**

Let $a, b, c$ be three integers which are pairwise coprime. Is every large integer
the sum of distinct integers of the form $a^k b^l c^m$ ($k, l, m ≥ 0$), none of which
divide any other?

Equivalently: is the set $\{a^k b^l c^m : k, l, m \geq 0\}$ d-complete?

Note: For this not to reduce to the two-integer case, we need the integers
to be greater than one and distinct.
-/
@[category research open, AMS 11]
theorem erdos_123 : answer(sorry) ↔ ∀ a > 1, ∀ b > 1, ∀ c > 1, PairwiseCoprime a b c →
    IsDComplete (↑(powers a) * ↑(powers b) * ↑(powers c)) := by sorry

/-!
## Proof of the Erdős-Lewin result for (3,5,7)

The proof follows Erdős-Lewin (1996) with the following structure:
1. Computational verification that all integers 186 ≤ n ≤ 2500 are d-representable
2. Density lemmas showing that {25^a · 7^b} and {5 · 25^a · 7^b} are dense enough
3. Strong induction reducing n > 2500 to smaller cases via mod-3 case analysis

The exceptions (integers ≤ 185 that are NOT d-representable) are exactly:
{2, 4, 6, 11, 13, 17, 18, 19, 20, 23, 29, 33, 37, 43, 51, 92, 100, 148, 185}

Key insight: Elements of form 25^a · 7^b ≡ 1 (mod 3) since 25 ≡ 7 ≡ 1 (mod 3).
Elements of form 5 · 25^a · 7^b ≡ 2 (mod 3) since 5 ≡ 2 (mod 3).
This allows reduction of any residue class mod 3 to the 0 (mod 3) case.
-/

/-- The set S = {3^k · 5^ℓ · 7^m : k, ℓ, m ≥ 0} -/
abbrev S357 : Set ℕ := ↑(powers 3) * ↑(powers 5) * ↑(powers 7)

/-- A number n is d-representable by S357 if it can be written as a sum of
    distinct elements of S357 forming an antichain under divisibility -/
def IsDRepresentable (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (s : Set ℕ) ⊆ S357 ∧ IsAntichain (· ∣ ·) (s : Set ℕ) ∧ s.sum id = n

/-- The finite set of exceptions (non-d-representable integers ≤ 185) -/
def exceptions : Finset ℕ :=
  {2, 4, 6, 11, 13, 17, 18, 19, 20, 23, 29, 33, 37, 43, 51, 92, 100, 148, 185}

/-!
### Density Lemmas

The key ratios are:
- 49/25 = 7²/25 ∈ (1, 2)
- 625/343 = 25²/7³ ∈ (1, 2)

This means from any m₀ = 25^a · 7^b, we can construct m₁ ∈ (m₀, 2m₀):
- If a ≥ 1: m₁ = m₀ · (7²/25) = 25^(a-1) · 7^(b+2)
- If a = 0 and b ≥ 3: m₁ = m₀ · (25²/7³) = 25² · 7^(b-3)
-/

/-- Key lemma: For X ≥ 343, there exists m ∈ {25^a · 7^b} with X < m < 2X.

Proof: Let m₀ be the largest element of M = {25^a · 7^b} with m₀ ≤ X.
- If m₀ = 25^a · 7^b with a ≥ 1, then m₁ := m₀ · (49/25) = 25^(a-1) · 7^(b+2) satisfies m₀ < m₁ < 2m₀
- If a = 0, then m₀ = 7^b ≥ 343 implies b ≥ 3, and m₁ := m₀ · (625/343) = 25² · 7^(b-3) works
By maximality of m₀, we have m₁ > X, hence m₁ ∈ (X, 2X). -/
lemma density_M (X : ℕ) (hX : X ≥ 343) :
    ∃ a b : ℕ, X < 25^a * 7^b ∧ 25^a * 7^b < 2 * X := by
  -- We construct the element using the density of {25^a · 7^b}
  -- The key ratios 49/25 < 2 and 625/343 < 2 ensure short intervals contain elements
  sorry

/-- Key lemma: For X ≥ 625, there exists m ∈ {5 · 25^a · 7^b} with X < m < 2X.

Proof: For X ≥ 1715, we have X/5 ≥ 343, so by Lemma 1 there exists u = 25^a · 7^b ∈ (X/5, 2X/5),
hence 5u ∈ (X, 2X).

For 625 ≤ X < 1715, we handle explicitly:
- 625 ≤ X < 875: take 5 · 25 · 7 = 875 ∈ (X, 2X)
- 875 ≤ X < 1715: take 5 · 7³ = 1715 ∈ (X, 2X) -/
lemma density_M5 (X : ℕ) (hX : X ≥ 625) :
    ∃ a b : ℕ, X < 5 * 25^a * 7^b ∧ 5 * 25^a * 7^b < 2 * X := by
  by_cases h1715 : X ≥ 1715
  · -- For X ≥ 1715, use density_M on X/5 ≥ 343
    have hX5 : X / 5 ≥ 343 := by omega
    obtain ⟨a, b, hlo, hhi⟩ := density_M (X / 5) hX5
    use a, b
    constructor
    · -- X < 5 * 25^a * 7^b follows from X/5 < 25^a * 7^b
      have h1 : X / 5 < 25^a * 7^b := hlo
      -- X ≤ 5 * (X/5) + 4 < 5 * (25^a * 7^b)
      have hX_bound : X ≤ 5 * (X / 5) + 4 := by
        have := Nat.div_add_mod X 5
        have hmod : X % 5 < 5 := Nat.mod_lt X (by norm_num)
        omega
      have h25_pos : 25^a * 7^b ≥ 1 := by
        have h1 : 25^a ≥ 1 := Nat.one_le_pow a 25 (by norm_num)
        have h2 : 7^b ≥ 1 := Nat.one_le_pow b 7 (by norm_num)
        exact one_le_mul h1 h2
      nlinarith
    · -- 5 * 25^a * 7^b < 2X follows from 25^a * 7^b < 2(X/5)
      have h2 : 25^a * 7^b < 2 * (X / 5) := hhi
      calc 5 * 25^a * 7^b = 5 * (25^a * 7^b) := by ring
        _ < 5 * (2 * (X / 5)) := by nlinarith
        _ = 10 * (X / 5) := by ring
        _ ≤ 2 * X := by omega
  · -- For 625 ≤ X < 1715, handle explicitly
    push_neg at h1715
    by_cases h875 : X < 875
    · -- 625 ≤ X < 875: use 5 · 25 · 7 = 875
      use 1, 1
      simp only [pow_one]
      constructor <;> omega
    · -- 875 ≤ X < 1715: use 5 · 7³ = 1715
      push_neg at h875
      use 0, 3
      simp only [pow_zero, pow_succ, pow_zero, one_mul]
      constructor <;> omega

/-- Base case: All integers in [186, 2500] are d-representable.
This requires computational verification via exhaustive search. -/
lemma base_case (n : ℕ) (hn_low : 186 ≤ n) (hn_high : n ≤ 2500) :
    IsDRepresentable n := by
  -- Computational verification: for each n in [186, 2500], there exists
  -- a subset of S357 that sums to n and forms an antichain under divisibility.
  -- The search space is manageable since |S357 ∩ [1, 2500]| is finite and small.
  sorry

/-- Auxiliary: multiplying by 3 preserves membership in S357 -/
lemma mul_three_mem_S357 {x : ℕ} (hx : x ∈ S357) : x * 3 ∈ S357 := by
  simp only [S357, Set.mem_mul] at hx ⊢
  obtain ⟨ab, hab, c, hc, rfl⟩ := hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hab
  -- a ∈ powers 3, b ∈ powers 5, c ∈ powers 7
  -- (a * b) * c * 3 = (a * 3) * b * c
  refine ⟨(a * 3) * b, ⟨a * 3, ?_, b, hb, rfl⟩, c, hc, by ring⟩
  -- Need: a * 3 ∈ powers 3
  obtain ⟨k, rfl⟩ := ha
  exact ⟨k + 1, by ring⟩

/-- Induction case 1: If n ≡ 0 (mod 3) and n/3 > 185, then n is d-representable.

Proof: If n/3 = s₁ + ... + sₜ is a valid d-representation, then n = 3s₁ + ... + 3sₜ.
The terms 3sᵢ are still distinct, lie in S357 (since 3 ∈ S357), and
3sᵢ ∣ 3sⱼ ⟺ sᵢ ∣ sⱼ, so no new divisibility relations are created. -/
lemma induction_case_mod0 (n : ℕ) (hn : n % 3 = 0) (_hn_large : n / 3 > 185)
    (ih : IsDRepresentable (n / 3)) : IsDRepresentable n := by
  obtain ⟨s, hs_sub, hs_anti, hs_sum⟩ := ih
  refine ⟨s.image (· * 3), ?_, ?_, ?_⟩
  · -- Show image ⊆ S357
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact mul_three_mem_S357 (hs_sub hy)
  · -- Antichain property preserved: 3sᵢ ∣ 3sⱼ ⟺ sᵢ ∣ sⱼ
    intro x hx y hy hxy h_dvd
    simp only [Finset.coe_image, Set.mem_image] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun heq => hxy (by simp [heq])
    have h3pos : (0 : ℕ) < 3 := by norm_num
    have hdiv' : x' ∣ y' := (Nat.mul_dvd_mul_iff_right h3pos).mp h_dvd
    exact hs_anti hx' hy' hne hdiv'
  · -- Sum preserved: Σ(3sᵢ) = 3 · Σsᵢ = 3 · (n/3) = n
    rw [Finset.sum_image]
    · simp only [id_eq, ← Finset.sum_mul]
      have hdiv : 3 ∣ n := Nat.dvd_of_mod_eq_zero hn
      have hsum : ∑ x ∈ s, x = n / 3 := hs_sum
      rw [hsum]
      exact Nat.div_mul_cancel hdiv
    · intro x _ y _ heq
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) heq

/-- Auxiliary: 25^a · 7^b ≡ 1 (mod 3) -/
lemma pow25_pow7_mod3 (a b : ℕ) : 25^a * 7^b % 3 = 1 := by
  have h25 : 25 % 3 = 1 := by norm_num
  have h7 : 7 % 3 = 1 := by norm_num
  have hp25 : 25^a % 3 = 1 := by
    induction a with
    | zero => simp
    | succ n ih => simp [pow_succ, Nat.mul_mod, ih, h25]
  have hp7 : 7^b % 3 = 1 := by
    induction b with
    | zero => simp
    | succ n ih => simp [pow_succ, Nat.mul_mod, ih, h7]
  simp [Nat.mul_mod, hp25, hp7]

/-- Auxiliary: 5 · 25^a · 7^b ≡ 2 (mod 3) -/
lemma five_pow25_pow7_mod3 (a b : ℕ) : 5 * 25^a * 7^b % 3 = 2 := by
  have h5 : 5 % 3 = 2 := by norm_num
  have h_inner : 25^a * 7^b % 3 = 1 := pow25_pow7_mod3 a b
  calc 5 * 25^a * 7^b % 3
      = 5 * (25^a * 7^b) % 3 := by ring_nf
    _ = (5 % 3) * (25^a * 7^b % 3) % 3 := by rw [Nat.mul_mod]
    _ = 2 * 1 % 3 := by rw [h5, h_inner]
    _ = 2 := by norm_num

/-- Auxiliary: elements of form 25^a · 7^b have gcd with 3 equal to 1 -/
lemma gcd_pow25_pow7_three (a b : ℕ) : Nat.gcd (25^a * 7^b) 3 = 1 := by
  have h25 : Nat.gcd 25 3 = 1 := by norm_num
  have h7 : Nat.gcd 7 3 = 1 := by norm_num
  have : Nat.gcd (25^a) 3 = 1 := Nat.Coprime.pow_left a h25
  have : Nat.gcd (7^b) 3 = 1 := Nat.Coprime.pow_left b h7
  exact Nat.Coprime.mul_left ‹Nat.gcd (25^a) 3 = 1› ‹Nat.gcd (7^b) 3 = 1›

/-- Auxiliary: elements of form 5 · 25^a · 7^b have gcd with 3 equal to 1 -/
lemma gcd_five_pow25_pow7_three (a b : ℕ) : Nat.gcd (5 * 25^a * 7^b) 3 = 1 := by
  have h5 : Nat.gcd 5 3 = 1 := by norm_num
  have h_inner : Nat.gcd (25^a * 7^b) 3 = 1 := gcd_pow25_pow7_three a b
  calc Nat.gcd (5 * 25^a * 7^b) 3
      = Nat.gcd (5 * (25^a * 7^b)) 3 := by ring_nf
    _ = 1 := Nat.Coprime.mul_left h5 h_inner

/-- Auxiliary: 25^a * 7^b is in S357 -/
lemma pow25_pow7_mem_S357 (a b : ℕ) : 25^a * 7^b ∈ S357 := by
  simp only [S357, Set.mem_mul]
  refine ⟨25^a, ⟨1, ?_, 25^a, ?_, by ring⟩, 7^b, ?_, rfl⟩
  · exact ⟨0, by ring⟩  -- 1 = 3^0 ∈ powers 3
  · use 2 * a
    have : (5 : ℕ)^2 = 25 := by norm_num
    calc 5^(2 * a) = (5^2)^a := by rw [pow_mul]
      _ = 25^a := by rw [this]
  · exact ⟨b, rfl⟩      -- 7^b ∈ powers 7

/-- Auxiliary: 5 · 25^a * 7^b is in S357 -/
lemma five_pow25_pow7_mem_S357 (a b : ℕ) : 5 * 25^a * 7^b ∈ S357 := by
  simp only [S357, Set.mem_mul]
  refine ⟨5 * 25^a, ⟨1, ?_, 5 * 25^a, ?_, by ring⟩, 7^b, ?_, by ring⟩
  · exact ⟨0, by ring⟩      -- 1 = 3^0 ∈ powers 3
  · use 2 * a + 1
    have : (5 : ℕ)^2 = 25 := by norm_num
    calc 5^(2 * a + 1) = 5^(2 * a) * 5^1 := by rw [pow_add]
      _ = (5^2)^a * 5 := by rw [pow_mul, pow_one]
      _ = 25^a * 5 := by rw [this]
      _ = 5 * 25^a := by ring
  · exact ⟨b, rfl⟩          -- 7^b ∈ powers 7

/-- Induction case 2: If N ≡ 1 (mod 3) and N > 2500, then N is d-representable.

Proof: Choose N' = 25^a · 7^b ∈ (N/4, N/2) using density_M (valid since N/4 > 625 > 343).
Since 25 ≡ 7 ≡ 1 (mod 3), we have N' ≡ 1 (mod 3), so N₁ := N - N' ≡ 0 (mod 3).
From N/4 < N' < N/2, we get N/2 < N₁ < 3N/4, hence N/6 < N₁/3 < N/4.
Since N > 2500, N₁/3 > 185, so by IH, N₁/3 has a d-representation.
Multiplying by 3 gives N₁ = 3t₁ + ... + 3tᵣ, and N = N' + 3t₁ + ... + 3tᵣ.

Antichain check: Each 3tᵢ is divisible by 3, but gcd(N', 3) = 1, so:
- 3tᵢ ∤ N' (since 3 ∤ N')
- N' ∤ 3tᵢ (since N' > N/4 > tᵢ for all tᵢ ≤ N₁/3 < N/4) -/
lemma induction_case_mod1 (n : ℕ) (hn : n % 3 = 1) (hn_large : n > 2500)
    (ih : ∀ m < n, m > 185 → IsDRepresentable m) : IsDRepresentable n := by
  -- Choose N' = 25^a · 7^b ∈ (n/4, n/2)
  have hX343 : n / 4 ≥ 343 := by omega
  obtain ⟨a, b, hlo, hhi⟩ := density_M (n / 4) hX343
  set N' := 25^a * 7^b with hN'
  -- N' ∈ (n/4, n/2)
  have hN'_lo : n / 4 < N' := hlo
  have hN'_hi : N' < n / 2 := by
    calc N' < 2 * (n / 4) := hhi
      _ ≤ n / 2 := by omega
  -- N' ≡ 1 (mod 3)
  have hN'_mod3 : N' % 3 = 1 := pow25_pow7_mod3 a b
  -- n - N' ≡ 0 (mod 3)
  have hN1_mod3 : (n - N') % 3 = 0 := by omega
  -- (n - N')/3 > 185 and < n
  have hN1_div3_large : (n - N') / 3 > 185 := by omega
  have hN1_div3_lt : (n - N') / 3 < n := by omega
  -- Apply IH to (n - N')/3
  obtain ⟨s, hs_sub, hs_anti, hs_sum⟩ := ih ((n - N') / 3) hN1_div3_lt hN1_div3_large
  -- Build representation: N = N' + 3t₁ + ... + 3tᵣ
  refine ⟨insert N' (s.image (· * 3)), ?_, ?_, ?_⟩
  · -- Subset of S357
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image] at hx
    rcases hx with heq | ⟨y, hy, rfl⟩
    · rw [heq]; exact pow25_pow7_mem_S357 a b
    · exact mul_three_mem_S357 (hs_sub hy)
  · -- Antichain property: N' coprime to 3, elements of s.image (*3) are divisible by 3
    -- Since gcd(N', 3) = 1, neither N' nor 3y' can divide the other (for y' ∈ s)
    -- Among 3x', 3y', the antichain property follows from that of x', y' in s
    sorry
  · -- Sum = n: N' + Σ(3·sᵢ) = N' + 3·Σsᵢ = N' + 3·((n-N')/3) = N' + (n-N') = n
    have hN'_lt_n : N' < n := by omega
    have hN'_nmem : N' ∉ s.image (· * 3) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro y _ heq
      have h3_dvd : 3 ∣ N' := ⟨y, by linarith [heq]⟩
      have : N' % 3 = 0 := Nat.mod_eq_zero_of_dvd h3_dvd
      omega
    simp only [Finset.sum_insert hN'_nmem]
    rw [Finset.sum_image]
    · simp only [id_eq, ← Finset.sum_mul]
      have hdiv3 : 3 ∣ (n - N') := Nat.dvd_of_mod_eq_zero hN1_mod3
      have hdiv3_eq : (n - N') / 3 * 3 = n - N' := Nat.div_mul_cancel hdiv3
      have hsum : ∑ x ∈ s, x = (n - N') / 3 := hs_sum
      rw [hsum]
      omega
    · intro x _ y _ h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) h

/-- Induction case 3: If N ≡ 2 (mod 3) and N > 2500, then N is d-representable.

Proof: Similar to Case 2, but using N'' = 5 · 25^a · 7^b ≡ 2 (mod 3). -/
lemma induction_case_mod2 (n : ℕ) (hn : n % 3 = 2) (hn_large : n > 2500)
    (ih : ∀ m < n, m > 185 → IsDRepresentable m) : IsDRepresentable n := by
  -- Choose N'' = 5 · 25^a · 7^b ∈ (n/4, n/2)
  have hX : n / 4 ≥ 625 := by omega
  obtain ⟨a, b, hlo, hhi⟩ := density_M5 (n / 4) hX
  set N'' := 5 * 25^a * 7^b with hN''
  -- N'' ∈ (n/4, n/2)
  have hN''_lo : n / 4 < N'' := hlo
  have hN''_hi : N'' < n / 2 := by
    calc N'' < 2 * (n / 4) := hhi
      _ ≤ n / 2 := by omega
  -- N'' ≡ 2 (mod 3)
  have hN''_mod3 : N'' % 3 = 2 := five_pow25_pow7_mod3 a b
  -- n - N'' ≡ 0 (mod 3)
  have hN2_mod3 : (n - N'') % 3 = 0 := by omega
  -- (n - N'')/3 > 185 and < n
  have hN2_div3_large : (n - N'') / 3 > 185 := by omega
  have hN2_div3_lt : (n - N'') / 3 < n := by omega
  -- Apply IH
  obtain ⟨s, hs_sub, hs_anti, hs_sum⟩ := ih ((n - N'') / 3) hN2_div3_lt hN2_div3_large
  refine ⟨insert N'' (s.image (· * 3)), ?_, ?_, ?_⟩
  · -- Subset of S357
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image] at hx
    rcases hx with heq | ⟨y, hy, rfl⟩
    · rw [heq]; exact five_pow25_pow7_mem_S357 a b
    · exact mul_three_mem_S357 (hs_sub hy)
  · -- Antichain property: Same structure as mod1 case
    sorry
  · -- Sum = n: N'' + Σ(3·sᵢ) = N'' + 3·Σsᵢ = N'' + 3·((n-N'')/3) = N'' + (n-N'') = n
    have hN''_lt_n : N'' < n := by omega
    have hN''_nmem : N'' ∉ s.image (· * 3) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro y _ heq
      have h3_dvd : 3 ∣ N'' := ⟨y, by linarith [heq]⟩
      have : N'' % 3 = 0 := Nat.mod_eq_zero_of_dvd h3_dvd
      omega
    simp only [Finset.sum_insert hN''_nmem]
    rw [Finset.sum_image]
    · simp only [id_eq, ← Finset.sum_mul]
      have hdiv3 : 3 ∣ (n - N'') := Nat.dvd_of_mod_eq_zero hN2_mod3
      have hdiv3_eq : (n - N'') / 3 * 3 = n - N'' := Nat.div_mul_cancel hdiv3
      have hsum : ∑ x ∈ s, x = (n - N'') / 3 := hs_sum
      rw [hsum]
      omega
    · intro x _ y _ h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) h

/-- Main theorem: Every n > 185 is d-representable by S357 -/
theorem erdos_lewin_main (n : ℕ) (hn : n > 185) : IsDRepresentable n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n ≤ 2500
    · exact base_case n hn h1
    · push_neg at h1
      mod_cases hn3 : n % 3
      · have hdiv3 : n / 3 > 185 := by omega
        have hlt : n / 3 < n := Nat.div_lt_self (by omega) (by norm_num)
        exact induction_case_mod0 n hn3 hdiv3 (ih (n/3) hlt hdiv3)
      · exact induction_case_mod1 n hn3 h1 (fun m hm hm' => ih m hm hm')
      · exact induction_case_mod2 n hn3 h1 (fun m hm hm' => ih m hm hm')

/--
Erdős and Lewin proved this conjecture when $a = 3$, $b = 5$, and $c = 7$.

Reference: [ErLe96] Erdős, P. and Lewin, Mordechai,
_$d$-complete sequences of integers_. Math. Comp. (1996), 837-840.
-/
@[category research solved, AMS 11]
theorem erdos_123.variants.erdos_lewin_3_5_7 :
    IsDComplete (↑(powers 3) * ↑(powers 5) * ↑(powers 7)) := by
  unfold IsDComplete
  rw [Filter.eventually_atTop]
  use 186
  intro n hn
  obtain ⟨s, hs_sub, hs_anti, hs_sum⟩ := erdos_lewin_main n (by omega)
  exact ⟨s, hs_sub, hs_anti, hs_sum⟩

/--
A simpler case: the set of numbers of the form $2^k 3^l$ ($k, l ≥ 0$) is d-complete.

This was initially conjectured by Erdős in 1992, who called it a "nice and difficult"
problem, but it was quickly proven by Jansen and others using a simple inductive argument:
- If $n = 2m$ is even, apply the inductive hypothesis to $m$ and double all summands.
- If $n$ is odd, let $3^k$ be the largest power of $3$ with $3^k ≤ n$, and apply the
  inductive hypothesis to $n - 3^k$ (which is even).

Reference: [Er92b] Erdős, Paul, _Some of my favourite problems in various branches
of combinatorics_. Matematiche (Catania) (1992), 231-240.
-/
@[category research solved, AMS 11]
theorem erdos_123.variants.powers_2_3 : IsDComplete (↑(powers 2) * ↑(powers 3)) := by sorry

/--
A stronger conjecture for numbers of the form $2^k 3^l 5^j$.

For any $ε > 0$, all large integers $n$ can be written as the sum of distinct integers
$b_1 < ... < b_t$ of the form $2^k 3^l 5^j$ where $b_t < (1 + ϵ) b_1$.
-/
@[category research open, AMS 11]
theorem erdos_123.variants.powers_2_3_5_snug :
    answer(sorry) ↔ ∀ ε > 0, ∀ᶠ n in atTop,
      ∃ A : Finset ℕ, (A : Set ℕ) ⊆ ↑(powers 2) * ↑(powers 3) * ↑(powers 5) ∧ IsSnug ε A ∧
        ∑ x ∈ A, x = n := by sorry

end Erdos123
