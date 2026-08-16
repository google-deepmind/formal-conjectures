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
# Number of Abelian cubes of length $3n$ over an alphabet of size 3

An Abelian cube is a string of the form $x x' x''$ with $|x| = |x'| = |x''|$ and $x$ is a
permutation of $x'$ and $x''$. The number of Abelian cubes of length $3n$ over an alphabet of
size 3 is given by
$$a(n) = \sum_{k=0}^n \binom{n}{k}^3 \sum_{j=0}^k \binom{k}{j}^3.$$

*References:*
- [A141057](https://oeis.org/A141057)-/

namespace OeisA141057

/-- Number of Abelian cubes of length $3n$ over an alphabet of size 3. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k ^ 3) * ∑ j ∈ Finset.range (k + 1), (k.choose j ^ 3)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 27 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 381 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6219 := by decide

/--
Conjecture: the supercongruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$ hold
for primes $p \ge 5$ and positive integers $n$ and $k$.-/
@[category research open, AMS 11]
theorem conjecture (p k n : ℕ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k)
    (h_n_pos : 1 ≤ n) :
    (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k))] := by
  sorry

end OeisA141057
