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
# Hyperperfect numbers

An integer $n > 1$ is called $k$-hyperperfect ($k \ge 1$, Minoli and Bear 1975) when
$n = 1 + k \cdot (\sigma_1(n) - n - 1)$, or equivalently $n + k(n + 1) = 1 + k \sigma_1(n)$;
setting $k = 1$ recovers `Nat.Perfect` (cf. `PerfectNumbers.infinitely_many_perfect`). Judson S.
McCranie (2000) conjectured that every $k$-hyperperfect integer with odd $k > 1$ has the form
$p^2 q$ for primes $p = (3k + 1) / 2$ and $q = 3k + 4$. At $k = 2$ (`OEIS A007593`), Alexander
Violette (June 2026) found a four-prime-factor $2$-hyperperfect counterexample outside the family
$n = 3^m(3^{m+1} - 2)$. Beyond Wikipedia's overview, Guy (2004, §B2) and the OEIS entries
`A007592` ($k \ge 2$) and `A007593` ($k = 2$) discuss whether infinitely many non-perfect
hyperperfect or $2$-hyperperfect integers exist.

*References:*
- [Wikipedia: Hyperperfect number](https://en.wikipedia.org/wiki/Hyperperfect_number)
- [OEIS A007592](https://oeis.org/A007592) (non-perfect hyperperfect integers, $k \ge 2$)
- [OEIS A007593](https://oeis.org/A007593) ($2$-hyperperfect integers, including A. Violette's June
  2026 counterexample)
- D. Minoli and R. Bear (1975), Pi Mu Epsilon J. **6**, no. 3, 153–157.
- [J. S. McCranie (2000)](https://cs.uwaterloo.ca/journals/JIS/VOL3/mccranie.html), J. Integer Seq.
  **3**, Article 00.1.3.
- Guy, R. K. (2004), Springer Problem Books in Math., §B2 (ISBN `978-0-387-20860-2`).
-/

@[expose] public section

namespace HyperperfectNumber

/-- Predicate asserting that $n > 1$ is $k$-hyperperfect ($k \ge 1$):
$n = 1 + k \cdot (s(n) - 1)$ where $s(n)$ sums the proper divisors of $n$. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ 1 < n ∧ n = 1 + k * ((∑ d ∈ n.properDivisors, d) - 1)

instance instDecidableRelIsHyperperfect : DecidableRel IsHyperperfect := fun k n ↦ by
  unfold IsHyperperfect
  infer_instance

/-- At $k = 1$, `IsHyperperfect 1 n` coincides with Mathlib's `Nat.Perfect n`. -/
@[category API, AMS 11]
theorem isHyperperfect_one_iff (n : ℕ) : IsHyperperfect 1 n ↔ n.Perfect := by
  rcases n with _ | _ | m
  · simp [IsHyperperfect, Nat.Perfect]
  · simp [IsHyperperfect, Nat.Perfect]
  · have hgt : 1 < m + 2 := by omega
    have h1 : 1 ∈ (m + 2).properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hgt
    have hge : 1 ≤ ∑ d ∈ (m + 2).properDivisors, d :=
      Finset.single_le_sum (f := fun d ↦ d) (fun _ _ ↦ Nat.zero_le _) h1
    simp only [IsHyperperfect, Nat.Perfect]
    omega

/-- Checks `IsHyperperfect` on $(k, n) = (1, 6), (1, 28), (2, 21), (3, 325)$, where
$325 = 5^2 \cdot 13$ illustrates McCranie's odd-$k$ prime pattern at $k = 3$. -/
@[category test, AMS 11]
theorem isHyperperfect_small_examples :
    IsHyperperfect 1 6 ∧ IsHyperperfect 1 28 ∧
      IsHyperperfect 2 21 ∧ IsHyperperfect 3 325 := by
  decide

/-- Excludes boundary and non-hyperperfect inputs $(0, 6), (2, 0), (2, 1), (2, 10)$. -/
@[category test, AMS 11]
theorem not_isHyperperfect_degenerate_and_ten :
    ¬ IsHyperperfect 0 6 ∧ ¬ IsHyperperfect 2 0 ∧
      ¬ IsHyperperfect 2 1 ∧ ¬ IsHyperperfect 2 10 := by
  decide

/--
McCranie's odd-$k$ conjecture (2000): for odd $k > 1$, every $k$-hyperperfect integer $n$ satisfies
$n = p^2 q$ with primes $p = (3k + 1)/2$ and $q = 3k + 4$.
-/
@[category research open, AMS 11]
theorem mccranie_odd_hyperperfect_conjecture {k n : ℕ} (hk_odd : Odd k) (hk : 1 < k)
    (hn : IsHyperperfect k n) :
    ((3 * k + 1) / 2).Prime ∧ (3 * k + 4).Prime ∧ n = ((3 * k + 1) / 2) ^ 2 * (3 * k + 4) := by
  sorry

/--
Not every $2$-hyperperfect integer has the form $3^m(3^{m+1} - 2)$ with $m \ge 1$ and $3^{m+1} - 2$
prime: Alexander Violette (June 2026, [OEIS A007593](https://oeis.org/A007593)) found the
four-prime-factor $2$-hyperperfect counterexample
$n = 3^{16} \cdot 129140227 \cdot 256572153302107 \cdot 225205396855537107298933866373$.
-/
@[category research solved, AMS 11]
theorem two_hyperperfect_characterization :
    ¬ ∀ n : ℕ, IsHyperperfect 2 n →
      ∃ m ≥ 1, (3 ^ (m + 1) - 2).Prime ∧ n = 3 ^ m * (3 ^ (m + 1) - 2) := by
  sorry

/--
Do infinitely many non-perfect hyperperfect integers ($k \ge 2$) exist (Guy 2004, §B2;
[OEIS A007592](https://oeis.org/A007592), not stated on Wikipedia; see
`PerfectNumbers.infinitely_many_perfect` for $k = 1$)?
-/
@[category research open, question, AMS 11]
theorem infinitely_many_hyperperfect_numbers :
    {n : ℕ | ∃ k ≥ 2, IsHyperperfect k n}.Infinite := by
  sorry

/--
Do infinitely many $2$-hyperperfect integers exist (Guy 2004, §B2;
[OEIS A007593](https://oeis.org/A007593), not stated on Wikipedia)?
-/
@[category research open, question, AMS 11]
theorem infinitely_many_hyperperfect_numbers.variants.two :
    {n : ℕ | IsHyperperfect 2 n}.Infinite := by
  sorry

end HyperperfectNumber
