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
# A110475: Number of symbols '*' and '^' to write the canonical prime factorization of n.

The canonical prime factorization is $n = p_1^{e_1} p_2^{e_2} \cdots p_k^{e_k}$.
The written form is $p_1^{\wedge} e_1 * p_2^{\wedge} e_2 * \cdots * p_k^{\wedge} e_k$,
where the $\wedge$ appears only if $e_i > 1$.
$a(n) = (\text{number of distinct prime factors}) - 1 + (\text{number of distinct prime factors with exponent } > 1)$.

*References:*
- [A110475](https://oeis.org/A110475)
-/

namespace OeisA110475

/-- 
The primary defining sequence `a`.
a(n) is the number of symbols '*' and '^' to write the canonical prime factorization of n.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let F := Nat.factorization n
  let S := F.support
  let num_distinct_primes := S.card
  let num_asterisks := num_distinct_primes - 1
  let num_carets := (S.filter fun p => F p > 1).card
  num_asterisks + num_carets



/-- The set of exceptional integers. -/
def exceptional_set : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 9, 11}

/--
It is conjectured that 1,2,3,4,5,6,7,9,11 are the only positive integers
which cannot be represented as the sum of two elements of indices $n$ such that $a(n) = 1$.
-/
@[category research open, AMS 11]
theorem main_conjecture :
  ∀ m > 0, m ∉ exceptional_set ↔ ∃ x y : ℕ, a x = 1 ∧ a y = 1 ∧ m = x + y := by
  sorry

end OeisA110475
