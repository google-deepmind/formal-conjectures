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
# Catalan-Larcombe-French sequence

The Catalan-Larcombe-French sequence defined by $a(0)=1$, $a(1)=8$, and
$$n^2 a(n) = 8(3n^2 - 3n + 1) a(n-1) - 128(n-1)^2 a(n-2)$$ for $n \ge 2$.

*References:*
- [A053175](https://oeis.org/A053175)-/

namespace OeisA53175

/-- Catalan-Larcombe-French sequence. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 8
  | n + 2 =>
    let n' := n + 2
    let an1 := a (n + 1)
    let an2 := a n
    let term1 := 8 * (3 * n' ^ 2 - 3 * n' + 1) * an1
    let term2 := 128 * (n' - 1) ^ 2 * an2
    (term1 - term2) / (n' ^ 2)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 8 := by
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 80 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 896 := by
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 10816 := by
  rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 137728 := by
  rfl

/-- The $(n+1) \times (n+1)$ Hankel-type matrix with $(i,j)$-entry $a(i+j)$. -/
def hankelMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦ (a (i.val + j.val) : ℤ)

/--
Conjecture: let $P(n)$ be the $(n+1) \times (n+1)$ Hankel-type determinant with $(i,j)$-entry
equal to $a(i+j)$ for all $i,j = 0, \ldots, n$. Then $P(n)/2^{n(n+3)}$ is a positive odd integer.
- Zhi-Wei Sun, Aug 14 2013
-/
@[category research open, AMS 11 15]
theorem conjecture (n : ℕ) :
    let detP := (hankelMatrix n).det
    let pow2 := (2 : ℤ) ^ (n * (n + 3))
    pow2 ∣ detP ∧ 0 < detP / pow2 ∧ (detP / pow2) % 2 = 1 := by
  sorry

end OeisA53175
