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
# Linear recurrence $a(n) = 5a(n-1) - 8a(n-2)$ with $a(0)=0, a(1)=1$

The sequence $a(n)$ satisfies the linear recurrence relation $a(n) = 5a(n-1) - 8a(n-2)$
with initial values $a(0) = 0$ and $a(1) = 1$.

*References:*
- [A190969](https://oeis.org/A190969)
- [Conjectures involving primes and quadratic forms](https://arxiv.org/abs/1211.1588)
  by *Zhi-Wei Sun*, arXiv:1211.1588 (2012)
-/

namespace OeisA190969

/--
The sequence defined by $a(0) = 0$, $a(1) = 1$, and $a(n+2) = 5a(n+1) - 8a(n)$.
-/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * a (n + 1) - 8 * a n

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 17 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 45 := by rfl

/--
The modular sum $S(p) = \sum_{k=0}^{p-1} \frac{a(4k) \binom{2k}{k}^3}{(-4096)^k}$ evaluated in
$\mathbb{Z}/p^m\mathbb{Z}$.
-/
def sMod (p m : ℕ) : ZMod (p ^ m) :=
  ∑ k ∈ Finset.range p,
    (a (4 * k) : ZMod (p ^ m)) * ((2 * k).choose k : ZMod (p ^ m)) ^ 3 *
      ((-4096 : ZMod (p ^ m)) ^ k)⁻¹

/--
Conjecture: Let $S(p) := \sum_{k=0}^{p-1} a(4k) \binom{2k}{k}^3 / (-4096)^k$.
Then $S(p) \equiv 0 \pmod{p^2}$ for every odd prime $p$.
- _Zhi-Wei Sun_, Mar 13 2013
-/
@[category research open, AMS 11]
theorem conjecture1 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    sMod p 2 = 0 := by
  sorry

/--
Conjecture: Let $S(p) := \sum_{k=0}^{p-1} a(4k) \binom{2k}{k}^3 / (-4096)^k$.
Then $S(p) \equiv 0 \pmod{p^3}$ for any odd prime $p \equiv 1, 2, 4 \pmod 7$.
- _Zhi-Wei Sun_, Mar 13 2013
-/
@[category research open, AMS 11]
theorem conjecture2 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h7 : p % 7 ∈ ({1, 2, 4} : Finset ℕ)) :
    sMod p 3 = 0 := by
  sorry

end OeisA190969
