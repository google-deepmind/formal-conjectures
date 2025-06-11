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
# Lemoine's conjectures

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/%C3%89mile_Lemoine#Lemoine's_conjecture_and_extensions)
- [Ki85] Kiltinen, J. and Young P. (1985). Goldbach, Lemoine, and a Know/Don't Know Problem.
-/

def OddPrime (n : ℕ) : Prop :=
  n ≠ 2 ∧ n.Prime

/--
For all odd integers $n ≥ 7$ there are prime numbers $p,q$ such that $n = p+2q$.
-/
@[category research open, AMS 11]
theorem lemoine_conjecture (n : ℕ) (hn : 6 < n) (odd : Odd n) :
    ∃ (p q : ℕ), p.Prime ∧ q.Prime ∧ p + 2 * q = n := by
  sorry

/--
For all odd integers $n ≥ 9$ there are odd prime numbers $p,q,r,s$ and natural numbers $a,b$
such that $p+2q = n$, $2+pq = 2^a+r$, $2p+q = 2^b+s$
-/
@[category research open, AMS 11]
theorem lemoine_conjecture_extension (n : ℕ) (hn : 8 < n) (odd : Odd n) :
    ∃ (p q r s a b : ℕ), OddPrime p ∧ OddPrime q ∧ OddPrime r ∧ OddPrime s ∧
    p + 2 * q = n ∧ 2 + p * q = 2 ^ a + r ∧ 2 * p + q = 2 ^ b + s := by
  sorry
