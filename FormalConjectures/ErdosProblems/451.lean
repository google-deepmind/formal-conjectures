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
# Erdős Problem 451

*References:*
- [erdosproblems.com/451](https://www.erdosproblems.com/451)
- [Er79d] Erdős, P., *Some unconventional problems in number theory*.
  Acta Math. Acad. Sci. Hungar. (1979), 71–80.
- [vDTa26] van Doorn, W. and Tang, Q., *Consecutive integers free of certain prime factors*.
  [arXiv:2606.19863](https://arxiv.org/abs/2606.19863) (2026).
-/

@[expose] public section

namespace Erdos451

open scoped BigOperators

/-- Exactly the primes in the strict interval `(k, 2*k)`. -/
def primeWindow (k : ℕ) : Finset ℕ :=
  (Finset.Ioo k (2 * k)).filter Nat.Prime

@[simp, category API, AMS 11]
theorem mem_primeWindow {k p : ℕ} :
    p ∈ primeWindow k ↔ k < p ∧ p < 2 * k ∧ p.Prime := by
  simp [primeWindow, and_assoc]

/-- The product $\prod_{1\le i\le k}(n-i)$. -/
def block (k n : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n - i)

/-- The exact condition from the source, expressed by bounded quantification. -/
def Admissible (k n : ℕ) : Prop :=
  2 * k < n ∧ ∀ p ∈ primeWindow k, ¬ p ∣ block k n

instance (k n : ℕ) : Decidable (Admissible k n) :=
  inferInstanceAs (Decidable (2 * k < n ∧ ∀ p ∈ primeWindow k, ¬ p ∣ block k n))

@[category API, AMS 11]
theorem admissible_iff_source (k n : ℕ) :
    Admissible k n ↔ 2 * k < n ∧
      ∀ p : ℕ, p.Prime → k < p → p < 2 * k → ¬ p ∣ block k n := by
  simp only [Admissible, mem_primeWindow]
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun p hp hkp hp2 => h p ⟨hkp, hp2, hp⟩⟩
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun p ⟨hkp, hp2, hp⟩ => h p hp hkp hp2⟩

/-- The product of the forbidden primes; the empty product is one. -/
def primeProduct (k : ℕ) : ℕ := ∏ p ∈ primeWindow k, p

@[category API, AMS 11]
theorem primeProduct_pos (k : ℕ) : 0 < primeProduct k := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_primeWindow.mp hp).2.2.pos

@[category API, AMS 11]
theorem prime_dvd_primeProduct {k p : ℕ} (hp : p ∈ primeWindow k) :
    p ∣ primeProduct k := Finset.dvd_prod_of_mem id hp

@[category API, AMS 11]
theorem prime_dvd_block_iff {k n p : ℕ} (hp : p.Prime) :
    p ∣ block k n ↔ ∃ i ∈ Finset.Icc 1 k, p ∣ n - i := by
  exact (Nat.prime_iff.mp hp).dvd_finsetProd_iff _

/-- Any multiple of all forbidden primes lying above `2*k` is admissible. -/
@[category API, AMS 11]
theorem admissible_of_multiple {k n : ℕ} (hn : 2 * k < n)
    (hm : primeProduct k ∣ n) : Admissible k n := by
  refine ⟨hn, ?_⟩
  intro p hp hbad
  have hkp := (mem_primeWindow.mp hp).1
  have hprime := (mem_primeWindow.mp hp).2.2
  obtain ⟨i, hi, hpi⟩ := (prime_dvd_block_iff hprime).mp hbad
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.mp hi
  have hpn : p ∣ n := (prime_dvd_primeProduct hp).trans hm
  have hle : i ≤ n := by omega
  have hd : p ∣ i := (Nat.dvd_sub_iff_right hle hpn).mp hpi
  have := Nat.le_of_dvd (by omega : 0 < i) hd
  omega

/-- A witness valid even for the small values where `primeProduct k ≤ 2*k`. -/
@[category API, AMS 11]
theorem admissible_witness (k : ℕ) :
    Admissible k ((2 * k + 1) * primeProduct k) := by
  apply admissible_of_multiple
  · have := primeProduct_pos k
    nlinarith
  · exact dvd_mul_left _ _

@[category API, AMS 11]
theorem exists_admissible (k : ℕ) : ∃ n, Admissible k n :=
  ⟨_, admissible_witness k⟩

/-- The least admissible integer $n_k$, extended to $k=0$. -/
def least (k : ℕ) : ℕ := Nat.find (exists_admissible k)

@[category API, AMS 11]
theorem least_admissible (k : ℕ) : Admissible k (least k) :=
  Nat.find_spec (exists_admissible k)

@[category API, AMS 11]
theorem two_mul_lt_least (k : ℕ) : 2 * k < least k :=
  (least_admissible k).1

@[category API, AMS 11]
theorem least_le {k n : ℕ} (hn : Admissible k n) : least k ≤ n :=
  Nat.find_min' (exists_admissible k) hn

@[category API, AMS 11]
theorem not_admissible_of_lt_least {k n : ℕ} (hn : n < least k) :
    ¬ Admissible k n := Nat.find_min (exists_admissible k) hn

@[category API, AMS 11]
theorem least_eq_iff (k n : ℕ) :
    least k = n ↔ Admissible k n ∧ ∀ m < n, ¬ Admissible k m := by
  constructor
  · rintro rfl
    exact ⟨least_admissible k, fun m hm => not_admissible_of_lt_least hm⟩
  · rintro ⟨hn, hmin⟩
    apply Nat.le_antisymm (least_le hn)
    by_contra h
    exact hmin (least k) (by omega) (least_admissible k)

@[category API, AMS 11]
theorem least_le_witness (k : ℕ) :
    least k ≤ (2 * k + 1) * primeProduct k := least_le (admissible_witness k)

/-- The simpler source upper bound, with its necessary small-value guard. -/
@[category API, AMS 11]
theorem least_le_primeProduct {k : ℕ} (hk : 2 * k < primeProduct k) :
    least k ≤ primeProduct k :=
  least_le (admissible_of_multiple hk (dvd_refl _))

/-- For a factor shorter than the prime modulus, divisibility fixes the residue. -/
@[category API, AMS 11]
theorem dvd_factor_iff_residue {k n p i : ℕ}
    (hn : 2 * k < n) (hp : k < p) (hi : i ∈ Finset.Icc 1 k) :
    p ∣ n - i ↔ n % p = i := by
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.mp hi
  have hip : i < p := by omega
  constructor
  · intro hd
    have heq : n = (n - i) + i := by omega
    calc
      n % p = ((n - i) + i) % p := congrArg (· % p) heq
      _ = i := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd,
                        Nat.mod_eq_of_lt hip, zero_add, Nat.mod_eq_of_lt hip]
  · intro h
    rw [← h]
    exact Nat.dvd_sub_mod n

@[category API, AMS 11]
theorem prime_dvd_block_iff_residue {k n p : ℕ}
    (hn : 2 * k < n) (hp : p.Prime) (hkp : k < p) :
    p ∣ block k n ↔ 1 ≤ n % p ∧ n % p ≤ k := by
  rw [prime_dvd_block_iff hp]
  constructor
  · rintro ⟨i, hi, hd⟩
    rw [dvd_factor_iff_residue hn hkp hi] at hd
    simpa [hd] using Finset.mem_Icc.mp hi
  · intro h
    exact ⟨n % p, Finset.mem_Icc.mpr h,
      (dvd_factor_iff_residue hn hkp (Finset.mem_Icc.mpr h)).mpr rfl⟩

/-- Admissibility is equivalent to avoiding the residues $1,\ldots,k$. -/
@[category API, AMS 11]
theorem admissible_iff_residues (k n : ℕ) :
    Admissible k n ↔ 2 * k < n ∧
      ∀ p ∈ primeWindow k, n % p = 0 ∨ k < n % p := by
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro p hp
    have hnd := h p hp
    rw [prime_dvd_block_iff_residue hn (mem_primeWindow.mp hp).2.2
      (mem_primeWindow.mp hp).1] at hnd
    omega
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    intro p hp hd
    have hr := (prime_dvd_block_iff_residue hn (mem_primeWindow.mp hp).2.2
      (mem_primeWindow.mp hp).1).mp hd
    have := h p hp
    omega

/-- An exact value of $n_k$. -/
@[category test, AMS 11]
theorem least_zero : least 0 = 1 := by
  apply (least_eq_iff 0 1).mpr
  constructor
  · decide
  · intro m hm
    interval_cases m; decide

/-- An exact value of $n_k$. -/
@[category test, AMS 11]
theorem least_one : least 1 = 3 := by
  apply (least_eq_iff 1 3).mpr
  constructor
  · decide
  · intro m hm
    interval_cases m <;> decide

/-- An exact value of $n_k$. -/
@[category test, AMS 11]
theorem least_two : least 2 = 6 := by
  apply (least_eq_iff 2 6).mpr
  constructor
  · decide
  · intro m hm
    interval_cases m <;> decide

/-- An exact value of $n_k$. -/
@[category test, AMS 11]
theorem least_three : least 3 = 9 := by
  apply (least_eq_iff 3 9).mpr
  constructor
  · decide
  · intro m hm
    interval_cases m <;> decide

/-- An exact value of $n_k$. -/
@[category test, AMS 11]
theorem least_four : least 4 = 20 := by
  apply (least_eq_iff 4 20).mpr
  constructor
  · decide
  · intro m hm
    interval_cases m <;> decide

/-- An exact value of $n_k$. -/
@[category test, AMS 11]
theorem least_five : least 5 = 13 := by
  apply (least_eq_iff 5 13).mpr
  constructor
  · decide
  · intro m hm
    interval_cases m <;> decide

/-- The prime-product upper bound needs a small-value guard: it fails at $k=2$. -/
@[category API, AMS 11]
theorem primeProduct_upper_bound_fails_at_two : primeProduct 2 < least 2 := by
  rw [least_two]
  decide

/-- The sequence $n_k$ eventually exceeds every positive real power of $k$. -/
def SuperpolynomialLower : Prop :=
  ∀ d : ℝ, 0 < d → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (k : ℝ) ^ d < (least k : ℝ)

/-- The sequence $n_k$ is eventually below $e^{\epsilon k}$ for every $\epsilon>0$. -/
def SubexponentialUpper : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    (least k : ℝ) < Real.exp (ε * (k : ℝ))

/-- The eventual quantitative lower bound of van Doorn and Tang [vDTa26]. -/
def VanDoornTangLower : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    Real.exp ((Real.log (k : ℝ)) ^ 2 /
      (20 * Real.log (Real.log (k : ℝ)))) < (least k : ℝ)

/-- Equivalent uniform formulation: every admissible candidate exceeds the bound. -/
@[category API, AMS 11]
theorem vanDoornTangLower_iff_all_admissible : VanDoornTangLower ↔
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ, Admissible k n →
      Real.exp ((Real.log (k : ℝ)) ^ 2 /
        (20 * Real.log (Real.log (k : ℝ)))) < (n : ℝ) := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro k hk n hn
    exact lt_of_lt_of_le (hK k hk) (by exact_mod_cast least_le hn)
  · rintro ⟨K, hK⟩
    exact ⟨K, fun k hk => hK k hk (least k) (least_admissible k)⟩

/--
Estimate $n_k$, the smallest integer $>2k$ such that
$\prod_{1\leq i\leq k}(n_k-i)$ has no prime factor in $(k,2k)$.

The lower-bound conjecture in [Er79d] asks whether $n_k>k^d$ for every constant $d$,
for all sufficiently large $k$. Van Doorn and Tang [vDTa26] proved this.
-/
@[category research solved, AMS 11]
theorem erdos_451.lower_bound : SuperpolynomialLower := by
  sorry

/--
In [Er79d] Erdős writes that probably $n_k<e^{o(k)}$.
Equivalently, for every $\epsilon>0$, we have $n_k<e^{\epsilon k}$ for all
sufficiently large $k$.
-/
@[category research open, AMS 11]
theorem erdos_451.upper_bound : SubexponentialUpper := by
  sorry

/--
Van Doorn and Tang [vDTa26] proved that
$n_k>\exp((\log k)^2/(20\log\log k))$ for all sufficiently large $k$.
-/
@[category research solved, AMS 11]
theorem erdos_451.variants.van_doorn_tang : VanDoornTangLower := by
  sorry

end Erdos451