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
# The binomial sums $\sum_{k=0}^{n-1} \binom{n-1}{k}^2 \binom{n+k}{k}$

The sequence is $a(n) = \sum_{k=0}^{n-1} \binom{n-1}{k}^2 \binom{n+k}{k}$ for $n \ge 0$, so
$a(0) = 0$.

*References:*
- [A361717](https://oeis.org/A361717), Peter Bala, 2023.
-/

@[expose] public section

namespace OeisA361717

/-- $a(n) = \sum_{k=0}^{n-1} \binom{n-1}{k}^2 \binom{n+k}{k}$. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (n - 1).choose k ^ 2 * (n + k).choose k

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 27 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 216 := by
  sorry

/--
"Conjecture 2: the supercongruence a(p-1) == 1 - 2*p - p^2 (mod p^3) holds for all primes except
p = 3 (checked up to p = 199)."
- Peter Bala, Mar 26 2023.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem conjecture_2 (p : ℕ) (hp : p.Prime) (h3 : p ≠ 3) :
    (a (p - 1) : ℤ) ≡ 1 - 2 * p - p ^ 2 [ZMOD p ^ 3] := by
  sorry

end OeisA361717

end
