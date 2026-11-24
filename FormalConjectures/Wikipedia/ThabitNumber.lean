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
# Thabit numbers and Thabit primes

For $n \ge 0$, the $n$-th *Thabit number* (of the first kind) is $K_n = 3 \cdot 2^n - 1$. In the
ninth century, Thābit ibn Qurra proved that whenever $n \ge 2$ makes $p = K_{n-1}$, $q = K_n$, and
$r = 9 \cdot 2^{2n - 1} - 1$ simultaneously prime, the integers $2^n p q$ and $2^n r$ form an
amicable pair (`IsAmicable`). Whether infinitely many Thabit primes exist, and whether Thābit ibn
Qurra's rule produces any amicable pair beyond the three known exponents $n = 2, 4, 7$ [Bo72, Gu04],
remain open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Thabit_number)
- [OEIS A055010](https://oeis.org/A055010)
- [OEIS A007505](https://oeis.org/A007505)
- [OEIS A002235](https://oeis.org/A002235)
- [Bo72] Borho, W. (1972). *On Thabit ibn Kurrah's formula for amicable numbers*, Math. Comp. 26
  (118), 571--578.
- [Gu04] Guy, R. K. (2004). *Unsolved Problems in Number Theory*, 3rd ed., Problem B4, Springer,
  New York. https://doi.org/10.1007/978-0-387-26677-0
-/

@[expose] public section

namespace ThabitNumber

/-- The $n$-th **Thabit number** of the first kind, $K_n = 3 \cdot 2^n - 1$
([OEIS A055010](https://oeis.org/A055010)). -/
def thabitNumber (n : ℕ) : ℕ := 3 * 2 ^ n - 1

/-- The Thabit numbers $K_n$ are prime for $n = 0, 1, 2, 3, 4$ ($2, 5, 11, 23, 47$) and composite at
$n = 5$ ($K_5 = 95 = 5 \cdot 19$). -/
@[category test, AMS 11]
theorem thabitNumber_small_values :
    (thabitNumber 0).Prime ∧ (thabitNumber 1).Prime ∧ (thabitNumber 2).Prime ∧
      (thabitNumber 3).Prime ∧ (thabitNumber 4).Prime ∧ ¬ (thabitNumber 5).Prime := by
  decide

/-- At $n = 2$, $p = K_1 = 5$, $q = K_2 = 11$, and $r = 71$ produce the classic amicable pair
$(220, 284)$. -/
@[category test, AMS 11]
theorem thabit_rule_amicable_220_284 :
    2 ^ 2 * thabitNumber 1 * thabitNumber 2 = 220 ∧
      2 ^ 2 * (9 * 2 ^ (2 * 2 - 1) - 1) = 284 ∧
      IsAmicable 220 284 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [isAmicable_iff]
  decide

/--
**Thābit ibn Qurra's amicable number theorem** [Bo72]: for $n \ge 2$, if $K_{n-1}$, $K_n$, and
$9 \cdot 2^{2n - 1} - 1$ are all prime, then $2^n K_{n-1} K_n$ and $2^n (9 \cdot 2^{2n - 1} - 1)$
form an amicable pair.

The hypothesis $n \ge 2$ excludes $n = 1$, where $K_0 = 2$ is not coprime to $2^n$.
-/
@[category textbook, AMS 11]
theorem thabit_amicable_rule {n : ℕ} (hn : 2 ≤ n) (hp : (thabitNumber (n - 1)).Prime)
    (hq : (thabitNumber n).Prime) (hr : (9 * 2 ^ (2 * n - 1) - 1).Prime) :
    IsAmicable (2 ^ n * thabitNumber (n - 1) * thabitNumber n)
      (2 ^ n * (9 * 2 ^ (2 * n - 1) - 1)) := by
  open ArithmeticFunction in
  -- Write `t = 2 ^ (n - 1)`; then `p + 1 = 3t`, `q + 1 = 6t`, `r + 1 = 18t²` and `2 ^ n = 2t`.
  set t := 2 ^ (n - 1) with ht
  have ht2 : 2 ≤ t := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2n : 2 ^ n = 2 * t := by
    rw [ht, ← pow_succ']
    congr 1
    omega
  have h2n1 : 2 ^ (2 * n - 1) = 2 * t ^ 2 := by
    rw [ht, ← pow_mul, ← pow_succ']
    congr 1
    omega
  have hp1 : thabitNumber (n - 1) + 1 = 3 * t := by
    unfold thabitNumber
    omega
  have hq1 : thabitNumber n + 1 = 6 * t := by
    unfold thabitNumber
    omega
  have hr1 : 9 * 2 ^ (2 * n - 1) - 1 + 1 = 18 * t ^ 2 := by
    have : 0 < t ^ 2 := by positivity
    omega
  have hs : sigma 1 (2 ^ n) + 1 = 4 * t := by
    rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq le_rfl, pow_succ, h2n]
    omega
  generalize thabitNumber (n - 1) = p at hp hp1 ⊢
  generalize thabitNumber n = q at hq hq1 ⊢
  generalize 9 * 2 ^ (2 * n - 1) - 1 = r at hr hr1 ⊢
  have hσ : ∀ {x : ℕ}, x.Prime → sigma 1 x = x + 1 := fun {x} hx => by
    have := sigma_one_apply_prime_pow (i := 1) hx
    simpa [Finset.sum_range_succ, add_comm] using this
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have c2p : Nat.Coprime (2 ^ n) p :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_left n
  have c2q : Nat.Coprime (2 ^ n) q :=
    ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_left n
  have c2r : Nat.Coprime (2 ^ n) r :=
    ((Nat.coprime_primes Nat.prime_two hr).mpr (by omega)).pow_left n
  have cpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  have hσa : sigma 1 (2 ^ n * p * q) = sigma 1 (2 ^ n) * (p + 1) * (q + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.mul_left c2q cpq),
      isMultiplicative_sigma.map_mul_of_coprime c2p, hσ hp, hσ hq]
  have hσb : sigma 1 (2 ^ n * r) = sigma 1 (2 ^ n) * (r + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime c2r, hσ hr]
  generalize sigma 1 (2 ^ n) = s at hs hσa hσb
  -- Pass to `ℤ`, where `s = 4t - 1`, `p = 3t - 1`, `q = 6t - 1` and `r = 18t² - 1`.
  have e1 : (s : ℤ) = 4 * t - 1 := by omega
  have e2 : (p : ℤ) = 3 * t - 1 := by omega
  have e3 : (q : ℤ) = 6 * t - 1 := by omega
  have e4 : (r : ℤ) = 18 * (t : ℤ) ^ 2 - 1 := by
    have : ((r + 1 : ℕ) : ℤ) = ((18 * t ^ 2 : ℕ) : ℤ) := by rw [hr1]
    push_cast at this
    linarith
  rw [isAmicable_iff, hσa, hσb, h2n]
  refine ⟨?_, ?_, ?_⟩
  · zify
    rw [e1, e2, e3, e4]
    ring
  · zify
    rw [e1, e2, e3, e4]
    ring
  · intro h
    have h' : (2 * (t : ℤ) * p * q) = 2 * t * r := by exact_mod_cast h
    rw [e2, e3, e4] at h'
    have ht' : (2 : ℤ) ≤ t := by exact_mod_cast ht2
    nlinarith

/--
There are infinitely many exponents $n \in \mathbb{N}$ ([OEIS A002235](https://oeis.org/A002235))
for which the Thabit number $K_n = 3 \cdot 2^n - 1$ is prime
([OEIS A007505](https://oeis.org/A007505)); since `thabitNumber` is injective, this is equivalent to
the infinitude of Thabit primes themselves.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Thabit_number)
-/
@[category research open, AMS 11]
theorem infinitely_many_thabit_primes : {n : ℕ | (thabitNumber n).Prime}.Infinite := by
  sorry

/--
Does there exist an integer $n > 7$ for which $K_{n-1}$, $K_n$, and $9 \cdot 2^{2n - 1} - 1$ are
simultaneously prime, yielding an amicable pair via Thābit ibn Qurra's rule [Bo72, Gu04]? Only
$n = 2, 4, 7$ are currently known.
-/
@[category research open, question, AMS 11]
theorem exists_thabit_amicable_exponent_gt_seven :
    ∃ n > 7, (thabitNumber (n - 1)).Prime ∧ (thabitNumber n).Prime ∧
      (9 * 2 ^ (2 * n - 1) - 1).Prime := by
  sorry

end ThabitNumber
