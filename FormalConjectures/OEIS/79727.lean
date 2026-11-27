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
public import FormalConjectures.OEIS.«3625»

/-!
# $a(n) = \sum_{k=0}^n \binom{2k}{k}^3$

The sequence $a(n) = 1 + \binom{2}{1}^3 + \binom{4}{2}^3 + \cdots + \binom{2n}{n}^3$:
$$a(n) = \sum_{k=0}^n \binom{2k}{k}^3$$

*References:*
- [A079727](https://oeis.org/A079727)-/

@[expose] public section

namespace OeisA79727

/-- $a(n) = \sum_{k=0}^n \binom{2k}{k}^3$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * k) k) ^ 3

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 9 := by
  rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 225 := by
  rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 8225 := by
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 351225 := by
  rfl

/--
Conjecture 1 (Peter Bala, 2024):
If prime $p$ is in A003625 then $a(p^2) \equiv 8 + p^2 \pmod{p^3}$.
-/
@[category research open, AMS 11]
theorem conjecture1 (p : ℕ) (hp : OeisA3625.A p) :
    a (p ^ 2) ≡ 8 + p ^ 2 [MOD p ^ 3] := by
  sorry

/--
Conjecture 2 (Peter Bala, 2024):
If prime $p$ is in A003625 then $a(p(p-1)) \equiv p^2 \pmod{p^3}$.
-/
@[category research open, AMS 11]
theorem conjecture2 (p : ℕ) (hp : OeisA3625.A p) :
    a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  sorry

/--
Conjecture 3 (Peter Bala, 2024):
If prime $p$ is in A003625 then $a((p^2-1)/2) \equiv p^2 \pmod{p^4}$.
-/
@[category research open, AMS 11]
theorem conjecture3 (p : ℕ) (hp : OeisA3625.A p) :
    a ((p ^ 2 - 1) / 2) ≡ p ^ 2 [MOD p ^ 4] := by
  sorry

/--
Conjecture 4 (Peter Bala, 2024):
If $n$ is a product of distinct primes from A003625 then $a((n-1)/2)$ is divisible by $n^2$.
-/
@[category research open, AMS 11]
theorem conjecture4 (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ a ((∏ p ∈ S, p - 1) / 2) := by
  sorry

section

open Finset

@[category API, AMS 11]
private theorem centralBinom_dvd_in_block_tail {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (q j : ℕ) (hjlo : (p - 1) / 2 < j) (hjhi : j < p) :
    p ∣ Nat.centralBinom (q * p + j) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hodd
  have hmod : (q * p + j) % p = j := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hjhi]
  have hdouble : 2 * (q * p + j) = (2 * q + 1) * p + (2 * j - p) := by
    have hpj : p ≤ 2 * j := by omega
    rw [Nat.add_mul, one_mul, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc,
      Nat.add_sub_of_le hpj]
  have hmodDouble : (2 * (q * p + j)) % p = 2 * j - p := by
    rw [hdouble]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show 2 * j - p < p by omega)]
  have hd := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := 2 * (q * p + j)) (k := q * p + j)
  have hz : (2 * j - p).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [hmod, hmodDouble, hz, zero_mul] at hd
  exact Nat.modEq_zero_iff_dvd.mp hd

@[category API, AMS 11]
private theorem full_blocks_dvd {p d : ℕ} (f : ℕ → ℕ)
    (hblock : ∀ q, d ∣ ∑ j ∈ range p, f (q * p + j)) (q : ℕ) :
    d ∣ ∑ j ∈ range (q * p), f j := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, sum_range_add]
    exact dvd_add ih (hblock q)

@[category API, AMS 11]
private theorem conjecture4_of_blocks
    (hfull : ∀ p, OeisA3625.A p → ∀ q,
      p ^ 2 ∣ ∑ j ∈ range p, (Nat.choose (2 * (q * p + j)) (q * p + j)) ^ 3)
    (hhalf : ∀ p, OeisA3625.A p → ∀ q,
      p ^ 2 ∣ ∑ j ∈ range ((p - 1) / 2 + 1),
        (Nat.choose (2 * (q * p + j)) (q * p + j)) ^ 3)
    (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ a ((∏ p ∈ S, p - 1) / 2) := by
  have hodd : Odd (∏ p ∈ S, p) := by
    refine Finset.prod_induction (s := S) id Odd (fun _ _ h₁ h₂ => h₁.mul h₂) odd_one fun p hp => ?_
    have hpS := hS p hp
    exact hpS.1.odd_of_ne_two (by rcases hpS.2 with h | h | h <;> omega)
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    have hc : Nat.Coprime p q :=
      (hS p hp).1.coprime_iff_not_dvd.mpr
        (fun hd => hpq (((hS q hq).1.dvd_iff_eq (hS p hp).1.ne_one).mp hd).symm)
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_pow_left_iff (by decide : 0 < (2 : ℕ)) _ _).mpr
        ((Nat.coprime_pow_right_iff (by decide : 0 < (2 : ℕ)) _ _).mpr hc))
  · intro p hp
    obtain ⟨s, hs⟩ := dvd_prod_of_mem (f := id) hp
    change ∏ i ∈ S, i = p * s at hs
    have hpS := hS p hp
    have hpt : Odd p := hpS.1.odd_of_ne_two (by rcases hpS.2 with h | h | h <;> omega)
    have hst : Odd s := by
      have h := hodd
      rw [hs] at h
      exact (Nat.odd_mul.mp h).2
    obtain ⟨q, hq⟩ := hst
    obtain ⟨t, ht⟩ := hpt
    have hn : (∏ i ∈ S, i) = 2 * (q * p + t) + 1 := by
      rw [hs, hq]
      calc
        p * (2 * q + 1) = 2 * (q * p) + p := by ring
        _ = 2 * (q * p + t) + 1 := by omega
    have hhalfIndex : ((∏ i ∈ S, i) - 1) / 2 = q * p + (p - 1) / 2 := by omega
    rw [hhalfIndex, a, Nat.add_assoc, sum_range_add]
    exact dvd_add (full_blocks_dvd (fun j => (Nat.choose (2 * j) j) ^ 3) (hfull p hpS) q)
      (hhalf p hpS q)

/-- Bala's fourth conjecture follows if, for each eligible prime $p$, each half-block
starting at a multiple of $p$ has sum divisible by $p^2$. -/
@[category API, AMS 11]
theorem conjecture4_of_half_blocks
    (hhalf : ∀ p, OeisA3625.A p → ∀ q,
      p ^ 2 ∣ ∑ j ∈ range ((p - 1) / 2 + 1),
        (Nat.choose (2 * (q * p + j)) (q * p + j)) ^ 3)
    (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ a ((∏ p ∈ S, p - 1) / 2) := by
  apply conjecture4_of_blocks _ hhalf S hS
  intro p hp q
  have hodd : Odd p := hp.1.odd_of_ne_two (by rcases hp.2 with h | h | h <;> omega)
  let k := (p - 1) / 2 + 1
  have hk : k ≤ p := by
    have := hp.1.two_le
    dsimp [k]
    omega
  let f (j : ℕ) := (Nat.choose (2 * (q * p + j)) (q * p + j)) ^ 3
  change p ^ 2 ∣ ∑ j ∈ range p, f j
  have hsplit := sum_range_add f k (p - k)
  rw [Nat.add_sub_of_le hk] at hsplit
  rw [hsplit]
  refine dvd_add (hhalf p hp q) (Finset.dvd_sum fun j hj => ?_)
  have hjlt := mem_range.mp hj
  have hd := centralBinom_dvd_in_block_tail hp.1 hodd q (k + j)
    (by dsimp [k]; omega) (by omega)
  obtain ⟨v, hv⟩ := hd
  refine ⟨p * v ^ 3, ?_⟩
  dsimp [f]
  rw [← Nat.centralBinom_eq_two_mul_choose, hv]
  ring

end

end OeisA79727

