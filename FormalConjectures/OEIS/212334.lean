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
# Balanced walks on a 4-dimensional cubic lattice with neighbor steps

Number of words, either empty or beginning with the first letter of the $4$-ary alphabet, where
each letter of the alphabet occurs $n$ times and letters of neighboring word positions are equal or
neighbors in the alphabet. Equivalently,
$$a(n) = \sum_{k=0}^{n-1} \binom{n}{k} \binom{n-1}{k} \binom{n+k-1}{k}^2$$
for $n \ge 1$ and $a(0) = 1$.

*References:*
- [A212334](https://oeis.org/A212334)
-/

namespace OeisA212334

/-- Number of words over a $4$-ary alphabet where each letter occurs $n$ times and adjacent
letters are equal or neighbors, given by
$a(n) = \sum_{k=0}^{n-1} \binom{n}{k} \binom{n-1}{k} \binom{n+k-1}{k}^2$ for $n \ge 1$ and
$a(0) = 1$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    ∑ k ∈ Finset.range n, n.choose k * (n - 1).choose k * (n + k - 1).choose k ^ 2

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 9 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 163 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3593 := by decide

/--
"It appears that for primes $p \ge 5$, $a(p) \equiv 1 \pmod{p^5}$."
- _Peter Bala_, Dec 12 2021
-/
@[category research open, AMS 11]
theorem conjecture1 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    a p % (p ^ 5) = 1 := by
  sorry

/--
"Conjecture: for $r \ge 2$, and all primes $p \ge 5$,
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$."
- _Peter Bala_, Oct 13 2022
-/
@[category research open, AMS 11]
theorem conjecture2 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr2 : 2 ≤ r) :
    a (p ^ r) % (p ^ (3 * r + 3)) = a (p ^ (r - 1)) % (p ^ (3 * r + 3)) := by
  sorry

end OeisA212334
