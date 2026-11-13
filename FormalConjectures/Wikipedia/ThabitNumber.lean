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
Qurra's rule generates infinitely many amicable pairs (only $n = 2, 4, 7$ are known), remain open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Thabit_number)
- [OEIS A007505](https://oeis.org/A007505)
- [Bo72] Borho, W. (1972). *On Thabit ibn Kurrah's formula for amicable numbers*, Math. Comp. 26
  (118), 571--578.
-/

@[expose] public section

namespace ThabitNumber

/-- The $n$-th **Thabit number** of the first kind, $K_n = 3 \cdot 2^n - 1$. -/
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
@[category research solved, AMS 11]
theorem thabit_amicable_rule {n : ℕ} (hn : 2 ≤ n) (hp : (thabitNumber (n - 1)).Prime)
    (hq : (thabitNumber n).Prime) (hr : (9 * 2 ^ (2 * n - 1) - 1).Prime) :
    IsAmicable (2 ^ n * thabitNumber (n - 1) * thabitNumber n)
      (2 ^ n * (9 * 2 ^ (2 * n - 1) - 1)) := by
  sorry

/--
There are infinitely many exponents $n \in \mathbb{N}$ for which the Thabit number
$3 \cdot 2^n - 1$ is prime ([OEIS A007505](https://oeis.org/A007505)).
-/
@[category research open, AMS 11]
theorem infinitely_many_thabit_primes : {n : ℕ | (thabitNumber n).Prime}.Infinite := by
  sorry

/--
Are there infinitely many integers $n \ge 2$ for which $K_{n-1}$, $K_n$, and
$9 \cdot 2^{2n - 1} - 1$ are simultaneously prime, yielding an amicable pair via Thābit ibn
Qurra's rule? Only $n = 2, 4, 7$ are currently known [Bo72].
-/
@[category research open, question, AMS 11]
theorem infinitely_many_thabit_amicable_exponents :
    {n : ℕ | 2 ≤ n ∧ (thabitNumber (n - 1)).Prime ∧ (thabitNumber n).Prime ∧
      (9 * 2 ^ (2 * n - 1) - 1).Prime}.Infinite := by
  sorry

end ThabitNumber
