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
# Central trinomial coefficients

Central trinomial coefficients: largest coefficient of $(1 + x + x^2)^n$, which is the coefficient
of $x^n$ in the expansion of $(1 + x + x^2)^n$.

*References:*
- [A002426](https://oeis.org/A002426)-/

namespace OeisA2426

/-- Central trinomial coefficients:
$a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} \binom{2k}{k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * (2 * k).choose k

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 7 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 19 := by rfl

/--
An integer $n > 3$ is prime if and only if $a(n) \equiv 1 \pmod{n^2}$.
We have verified this for $n$ up to $8 \cdot 10^5$, and proved that $a(p) \equiv 1 \pmod{p^2}$
for any prime $p > 3$ (cf. A277640).
- Zhi-Wei Sun, Nov 30 2016-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 3 < n) :
    n.Prime ↔ a n ≡ 1 [MOD n ^ 2] := by
  sorry

end OeisA2426
