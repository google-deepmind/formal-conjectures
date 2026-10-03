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
# Alternating sum of fourth powers of binomial coefficients

The sequence is defined by
$$a(n) = \sum_{k=0}^n \binom{n}{k}^4 (-1)^k.$$

*References:*
- [A228304](https://oeis.org/A228304)
-/

namespace OeisA228304

open Matrix

/-- Alternating sum of fourth powers of binomial coefficients:
$$a(n) = \sum_{k=0}^n \binom{n}{k}^4 (-1)^k.$$ -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 4

/-- Auxiliary sequence:
$$c(n) = \sum_{k=0}^n (-1)^k \binom{n}{k}^2 \binom{2k}{k} \binom{2(n-k)}{n-k}.$$ -/
def c (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2 * ((2 * k).choose k : ℤ) *
      ((2 * (n - k)).choose (n - k) : ℤ)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = -14 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 786 := by decide

/--
Conjecture: Let $p$ be any odd prime, and let $A(p)$ be the $p \times p$ determinant with
$(i,j)$-entry equal to $a(i+j)$ for all $i, j = 0, \dots, p-1$. Then
$A(p) \equiv (-1)^{(p-1)/2} \pmod p$. Similarly, if $C(p)$ is the $p \times p$ determinant with
$(i,j)$-entry equal to $c(i+j)$ for all $i, j = 0, \dots, p-1$, then $C(p) \equiv 1 \pmod p$.
-/
@[category research open, AMS 11]
theorem conjecture1 (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    let A : Matrix (Fin p) (Fin p) ℤ := fun i j => a (i.val + j.val)
    let C : Matrix (Fin p) (Fin p) ℤ := fun i j => c (i.val + j.val)
    A.det ≡ (-1 : ℤ) ^ ((p - 1) / 2) [ZMOD p] ∧ C.det ≡ 1 [ZMOD p] := by
  sorry

end OeisA228304
