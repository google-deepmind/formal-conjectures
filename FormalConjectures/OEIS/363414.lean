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

import FormalConjecturesUtil

/-!
# Imaginary part of $\prod_{k=0}^n (1 + 2k i)$

The sequence is defined by
$$a(n) = \frac{1}{2} \operatorname{Im}\left( \prod_{k=0}^n (1 + 2k i) \right)$$

*References:*
- [A363414](https://oeis.org/A363414)
-/
open Nat Finset Complex Real Filter Asymptotics ZMod Int

namespace OeisA363414

/--
$a(n) = \frac{1}{2} \operatorname{Im}\left( \prod_{k=0}^n (1 + 2k i) \right)$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Complex :=
    Finset.prod (range (n + 1))
    (fun k : ℕ ↦ (1 : Complex) + ((2 * k : ℕ) : ℝ) * Complex.I)

  Int.floor (P_n.im / 2)

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by norm_num [a, Finset.prod_range_succ]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by norm_num [a, Finset.prod_range_succ]

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by norm_num [a, Finset.prod_range_succ]

@[category test, AMS 11]
theorem a_3 : a 3 = -18 := by norm_num [a, Finset.prod_range_succ]

@[category test, AMS 11]
theorem a_4 : a 4 = -190 := by norm_num [a, Finset.prod_range_succ]

/--
The set of primes of type 2 for a is conjecturally
$\mathbb{P}_2 = \{p \mid p \equiv 1 \pmod 4\}$.
-/
def type_two_primes_conjectured : Set ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod 4) = 1}

/--
Conjecture:
The set of type 1 primes is empty; every prime $p$ divides some term $a(n)$ with $n > 0$.
-/
@[category research open, AMS 11]
theorem conjecture_type1_empty :
  ∀ p : ℕ, p.Prime → ∃ n : ℕ, 0 < n ∧ (p : ℤ) ∣ a n := by sorry

/--
Moll's conjecture 5.5 extends to this sequence:
for the primes of type 2, the p-adic valuation $\nu_p(a(n)) \sim n/(p - 1)$ as $n \to \infty$.
This is formalized using asymptotic equivalence (`~[atTop]`) for the p-adic valuation
(`padicValInt`) converted to a real number.
-/
@[category research open, AMS 11]
theorem conjecture_type2_asymptotics :
  ∀ p : ℕ, p.Prime → p ∈ type_two_primes_conjectured →
  (fun n ↦ (padicValInt p (a n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) / ((p : ℝ) - 1)) := by sorry

end OeisA363414
