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


public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

/-!
# Three-prime smooth-prefix least common multiples

For three pairwise distinct primes, this file identifies the least common
multiple of all generated smooth numbers below a cutoff with the product of
the three largest corresponding pure prime powers.

This is a finite structural identity. It does not establish rationality,
irrationality or transcendence of the series appearing in Erdős Problem 269.
-/

namespace Erdos269

/-- The `{p, q, r}`-smooth lattice point with exponent vector `(i, j, k)`. -/
def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

/--
The product of the largest pure `p`-, `q`- and `r`-powers not exceeding `x`.
For pairwise distinct primes and every non-zero cutoff, this is the least
common multiple of all `{p, q, r}`-smooth numbers at most `x`.
-/
def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

/--
Exponent vectors of the actual `{p, q, r}`-smooth prefix up to `x`.
The logarithmic box makes the set finite; the final filter retains exactly the
products that do not exceed the cutoff.
-/
def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)) ×ˢ
      ((Finset.range (Nat.log q x + 1)) ×ˢ
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x

/-- The literal least common multiple of the finite smooth prefix. -/
def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2

/--
Every actual smooth-prefix value divides the product of the coordinatewise
maximal pure powers.
-/
theorem smooth3Val_dvd_threePrimeHeight_of_mem
    {p q r x : ℕ} {e : ℕ × ℕ × ℕ}
    (he : e ∈ smoothPrefixExponents p q r x) :
    smooth3Val p q r e.1 e.2.1 e.2.2 ∣ threePrimeHeight p q r x := by
  rw [smoothPrefixExponents, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product] at he
  obtain ⟨⟨hp, hq, hr⟩, -⟩ := he
  rw [Finset.mem_range, Nat.lt_succ_iff] at hp hq hr
  exact mul_dvd_mul
    (mul_dvd_mul (pow_dvd_pow p hp) (pow_dvd_pow q hq))
    (pow_dvd_pow r hr)

/-- The smooth-prefix LCM divides the three-prime height. -/
theorem smoothPrefixLcm_dvd_threePrimeHeight (p q r x : ℕ) :
    smoothPrefixLcm p q r x ∣ threePrimeHeight p q r x :=
  Finset.lcm_dvd fun _ he => smooth3Val_dvd_threePrimeHeight_of_mem he

/-- The maximal pure `p`-power occurs in every non-empty cutoff prefix. -/
theorem pureFirst_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (Nat.log p x, 0, 0) ∈ smoothPrefixExponents p q r x := by
  rw [smoothPrefixExponents, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simp [Finset.mem_product, Nat.lt_succ_iff]
  · simpa [smooth3Val] using Nat.pow_log_le_self p hx

/-- The maximal pure `q`-power occurs in every non-empty cutoff prefix. -/
theorem pureSecond_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (0, Nat.log q x, 0) ∈ smoothPrefixExponents p q r x := by
  rw [smoothPrefixExponents, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simp [Finset.mem_product, Nat.lt_succ_iff]
  · simpa [smooth3Val] using Nat.pow_log_le_self q hx

/-- The maximal pure `r`-power occurs in every non-empty cutoff prefix. -/
theorem pureThird_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (0, 0, Nat.log r x) ∈ smoothPrefixExponents p q r x := by
  rw [smoothPrefixExponents, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simp [Finset.mem_product, Nat.lt_succ_iff]
  · simpa [smooth3Val] using Nat.pow_log_le_self r hx

/--
For three pairwise distinct primes and a non-zero cutoff, the smooth-prefix
LCM is exactly the product of the three largest pure prime powers below the
cutoff.
-/
theorem smoothPrefixLcm_eq_threePrimeHeight_of_ne_zero
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x := by
  refine Nat.dvd_antisymm (smoothPrefixLcm_dvd_threePrimeHeight p q r x) ?_
  have hpDvd : p ^ Nat.log p x ∣ smoothPrefixLcm p q r x := by
    have h :=
      Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureFirst_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx)
    simpa [smoothPrefixLcm, smooth3Val] using h
  have hqDvd : q ^ Nat.log q x ∣ smoothPrefixLcm p q r x := by
    have h :=
      Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureSecond_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx)
    simpa [smoothPrefixLcm, smooth3Val] using h
  have hrDvd : r ^ Nat.log r x ∣ smoothPrefixLcm p q r x := by
    have h :=
      Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureThird_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx)
    simpa [smoothPrefixLcm, smooth3Val] using h
  have hpqCoprime : (p ^ Nat.log p x).Coprime (q ^ Nat.log q x) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
  have hprCoprime : (p ^ Nat.log p x).Coprime (r ^ Nat.log r x) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hr).mpr hpr)
  have hqrCoprime : (q ^ Nat.log q x).Coprime (r ^ Nat.log r x) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hr).mpr hqr)
  have hpqDvd :
      p ^ Nat.log p x * q ^ Nat.log q x ∣ smoothPrefixLcm p q r x :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hpqCoprime hpDvd hqDvd
  have hpqrCoprime :
      (p ^ Nat.log p x * q ^ Nat.log q x).Coprime (r ^ Nat.log r x) :=
    Nat.coprime_mul_iff_left.mpr ⟨hprCoprime, hqrCoprime⟩
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hpqrCoprime hpqDvd hrDvd

/-- At the zero cutoff the smooth prefix is empty, so both sides equal `1`. -/
theorem smoothPrefixLcm_zero_eq_threePrimeHeight_zero (p q r : ℕ) :
    smoothPrefixLcm p q r 0 = threePrimeHeight p q r 0 := by
  simp [smoothPrefixLcm, threePrimeHeight, smoothPrefixExponents, smooth3Val,
    Finset.filter_singleton]

/--
For three pairwise distinct primes and **every** cutoff, the least common
multiple of the `{p, q, r}`-smooth numbers at most `x` is the product of the
largest pure `p`-, `q`- and `r`-powers at most `x`.
-/
theorem smoothPrefixLcm_eq_threePrimeHeight
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (x : ℕ) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    exact smoothPrefixLcm_zero_eq_threePrimeHeight_zero p q r
  · exact smoothPrefixLcm_eq_threePrimeHeight_of_ne_zero hp hq hr hpq hpr hqr
      hx.ne'

end Erdos269
