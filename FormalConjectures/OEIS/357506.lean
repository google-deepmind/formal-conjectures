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
# Product of Apéry numbers $B(n)^3 B(n-1)$

The sequence is defined by $a(n) = B(n)^3 B(n-1)$, where $B(n) = \sum_{k=0}^n \binom{n}{k}^2
\binom{n+k}{k}$
are the Apéry numbers (A005258).

*References:*
- [A357506](https://oeis.org/A357506)
-/
open Nat Finset

namespace OeisA357506

/--
A005258(n): The Apéry numbers $B(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}$.
-/
def A005258 (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * ((n + k).choose k)

/--
$a(n) = B(n)^3 B(n-1)$ for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  (A005258 n) ^ 3 * (A005258 (n - 1))

@[category test, AMS 11]
theorem a_1 : a 1 = 27 := by
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 20577 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 60353937 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 287798988897 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 1782634331587527 := by rfl

/--
The stronger congruence $a(p) \equiv 27 \pmod{p^5}$ holds for all primes $p \ge 3$.
-/
@[category research open, AMS 11]
theorem conjecture_1 : ∀ (p : ℕ), p.Prime → 3 ≤ p → a p ≡ 27 [MOD (p ^ 5)] := by
  sorry

/--
For $r \ge 2$, $a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for all primes $p \ge 5$.
Peter Bala, Oct 13 2022
-/
@[category research open, AMS 11]
theorem conjecture_2 :
    ∀ (p r : ℕ), p.Prime → 5 ≤ p → 2 ≤ r →
      a (p ^ r) ≡ a (p ^ (r - 1)) [MOD p ^ (3 * r + 3)] := by
  sorry

end OeisA357506
