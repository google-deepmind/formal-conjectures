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
# Conjecture A102371

The sequence $a(n)$ is defined by the recurrence relation $a(1)=1$, and for $n>1$, $a(n) = a(n-1) \operatorname{XOR} (a(n-1) + n)$.
The conjecture asks if $a(n) = 2^n - 1 - \operatorname{A105033}(n-1)$ for $n \ge 1$.

*References:*
- [A102371](https://oeis.org/A102371)
-/

namespace OeisA102371

open Nat
open Int

/-- The primary defining sequence `a`.
$a(n)$ is defined by the recurrence relation $a(1)=1$, and for $n>1$, $a(n) = a(n-1) \operatorname{XOR} (a(n-1) + n)$,
where $\operatorname{XOR}$ is the bitwise exclusive-or operator (`^^^`). -/
def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n' + 2) =>
  let an_minus_1 := a (n' + 1)
  an_minus_1 ^^^ (an_minus_1 + (n' + 2))

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 7 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 12 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 29 := by rfl

/-- A105033: The number of positive integers $k$ such that $2^k$ divides $n-k$.
This is defined as the cardinality of the set of such $k$. The set is finite
for any fixed $n$. -/
noncomputable def a105033 (n : ℕ) : ℕ :=
  Nat.card { k : ℕ // 0 < k ∧ (2^k : ℤ) ∣ (Int.ofNat n - Int.ofNat k) }

/--
Do we have $a(n) = 2^n - 1 - \operatorname{A105033}(n-1)$ for $n \ge 1$?

Note: The OEIS comment suggests $n-1$ which means this applies at least for $n \ge 1$,
as we assume $\operatorname{A105033}(\mathbb{N})$ is defined on $\mathbb{N}$.
We include the case $n=1$ which relies on $A105033(0)$, which is 0.
-/
@[category research open, AMS 11]
theorem conjecture : answer(sorry) ↔ ∀ n : ℕ, 0 < n → a n = 2^n - 1 - a105033 (n - 1) := by
  sorry

end OeisA102371
