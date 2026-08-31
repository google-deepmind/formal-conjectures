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
# Numerator of $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right)$

Conjecture: $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right) = A005156(n+1)/A005156(n)$

*References:*
- [A109074](https://oeis.org/A109074)
-/

namespace OeisA109074

open Nat

/--
The rational number defined by $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right)$,
whose numerator is A109074.
-/
def frac (n : ℕ) : ℚ :=
  let numTerm : ℕ := (6 * n - 2).choose (2 * n)
  let denTerm : ℕ := 2 * ((4 * n - 1).choose (2 * n))
  (numTerm : ℚ) / (denTerm : ℚ)

/--
The primary defining sequence `a`.
$a(n)$ is the numerator of $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right)$.
-/
def a (n : ℕ) : ℕ :=
  (frac n).num.natAbs

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by native_decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 26 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 323 := by native_decide

/--
A005156 (offset 0): the number of vertically symmetric alternating sign matrices of order
$2n+1$, given by $a(n) = \frac{1}{2^n} \prod_{k=1}^{n} \frac{(6k-2)!\,(2k-1)!}{(4k-1)!\,(4k-2)!}$.
-/
def b (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.Icc 1 n, ((6 * k - 2)! * (2 * k - 1)!)) /
    (2 ^ n * ∏ k ∈ Finset.Icc 1 n, ((4 * k - 1)! * (4 * k - 2)!))

@[category test, AMS 11]
theorem b_0 : b 0 = 1 := by native_decide

@[category test, AMS 11]
theorem b_1 : b 1 = 1 := by native_decide

@[category test, AMS 11]
theorem b_2 : b 2 = 3 := by native_decide

@[category test, AMS 11]
theorem b_3 : b 3 = 26 := by native_decide

@[category test, AMS 11]
theorem b_4 : b 4 = 646 := by native_decide

/--
It is conjectured that binomial(6*n-2,2*n)/(2 * binomial(4*n-1,2*n)) = A005156(n+1)/A005156(n),
where the OEIS comment reads A005156 as 1-based; with the 0-indexed `b` this is
`frac (n + 1) = b (n + 1) / b n`.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) :
    frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ) := by
  sorry

end OeisA109074
