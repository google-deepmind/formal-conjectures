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
# Decimal encoding of the prime factorization of $n$

If $n$ has prime factorization $p_1^{e_1} \dots p_r^{e_r}$ with $p_1 < \dots < p_r$,
then its decimal encoding is $p_1 e_1 \dots p_r e_r$.

*References:*
- [A067599](https://oeis.org/A067599)
-/

namespace OeisA67599

/-- Concatenates two natural numbers $a$ and $b$ base 10. -/
def concatenateNats (a b : ℕ) : ℕ :=
  a * (10 ^ (Nat.digits 10 b).length) + b

/-- Decimal encoding of the prime factorization of $n$. -/
def a (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let factors : List ℕ := n.primeFactorsList.dedup
    let flat_list : List ℕ := factors.flatMap fun p ↦ [p, n.primeFactorsList.count p]
    flat_list.foldl concatenateNats 0

@[category test, AMS 11]
theorem a_2 : a 2 = 21 := by
  decide +native

@[category test, AMS 11]
theorem a_3 : a 3 = 31 := by
  decide +native

@[category test, AMS 11]
theorem a_4 : a 4 = 22 := by
  decide +native

@[category test, AMS 11]
theorem a_5 : a 5 = 51 := by
  decide +native

@[category test, AMS 11]
theorem a_6 : a 6 = 2131 := by
  decide +native

/--
"$a(31) = a(177147) = 311$. Is there any solution to $a(n) = n$?
- _Franklin T. Adams-Watters_, Dec 18 2006"
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔ ∃ n : ℕ, 2 ≤ n ∧ a n = n := by
  sorry

end OeisA67599
