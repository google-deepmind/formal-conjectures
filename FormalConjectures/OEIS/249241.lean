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
# Difference between product of composite numbers and the next prime number where this is $>1$

The sequence is:

Take the product of all composite numbers $\le p_n$ where $p_n$ is the $n$-th prime ($0$-indexed here, $1$-indexed in OEIS).

Calculate the difference to the smallest prime number that is at least this product $+2$. This should be a positive number $\ge 2$.

This difference is $a(n)$.

*References:*
- [A249241](https://oeis.org/A249241)-/

@[expose] public section

namespace OeisA249241

/-- The $n$-th prime. $0$-indexed here, $1$-indexed in OEIS. -/
noncomputable abbrev nthPrime (n : ℕ) := Nat.nth Nat.Prime n

/--
The smallest prime $\ge n$.

Modeled after `7918.lean`. -/
noncomputable def nextPrime (n : ℕ) : ℕ :=
  sInf { p : ℕ | p.Prime ∧ n ≤ p }

/-- The sequence $a$ -/
noncomputable def a (n : ℕ) : ℕ :=
  let pn := nthPrime n
  let frac := Nat.factorial pn / primorial pn
  nextPrime (frac + 2) - frac

/-- Conjecture: All terms are prime. -/
@[category research open, AMS 11]
theorem conjecture : ∀ n, Nat.Prime (a n) := by
  sorry

end OeisA249241
