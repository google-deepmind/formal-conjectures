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
# Sequence related to NOR bracketings

$$a(n) = \sum_{j=0}^{n-1} (-1)^j \binom{2j}{j} \binom{2n-j-2}{n-j-1}$$

*References:*
- [A112521](https://oeis.org/A112521)
-/

namespace OeisA112521

open Nat Int Finset

/--
`a n` is the $n$-th term of the sequence related to NOR bracketings.
-/
def a (n : ℕ) : ℕ :=
  (∑ j ∈ range n,
    let c1 : ℕ := (2 * j).choose j
    let c2Top : ℕ := 2 * n - (j + 2)
    let c2Bot : ℕ := n - (j + 1)
    let c2 : ℕ := c2Top.choose c2Bot
    let termMagnitude : ℤ := c1 * c2

    if j % 2 = 0 then termMagnitude else -termMagnitude
  ).toNat

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 6 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 60 := by decide

/--
`T n k` is the array defined as $T(1,1) = 1$, $T(i,j) = 0$ if $i<1$ or $j<1$,
$T(n,k) = T(n,k-2) + T(n,k-1) - 2 T(n-1,k-1) + T(n-1,k) + T(n-2,k)$.
-/
def T (n k : ℕ) : ℤ :=
  if n = 0 ∨ k = 0 then 0
  else if n = 1 ∧ k = 1 then 1
  else
    T n (k - 2) + T n (k - 1) - 2 * T (n - 1) (k - 1) + T (n - 1) k + T (n - 2) k
termination_by n + k

/--
Conjecture: Starting with $n=1$, $a(n)$ is the main diagonal of the array $T(n, k)$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a112521-formal-conjectures/blob/d4ee80e997c20209a1f18b7b9aa3521150d5474d/lean/OeisA112521Proof.lean#L876-L885"]
theorem conjecture : ∀ (n : ℕ), n ≥ 1 → (a n : ℤ) = T n n := by
  sorry

end OeisA112521
