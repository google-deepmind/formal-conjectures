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
# Number of squares $\bmod n$

The number of squares modulo $n$.
This is the cardinality of the set $\{k^2 \bmod n \mid k \in \{0, 1, \dots, n-1\}\}$.

*References:*
- [A000224](https://oeis.org/A000224)
-/

namespace OeisA224

/-- The number of squares modulo $n$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

/--
$n^2 \equiv 1 \pmod{a(n)(a(n)-1)}$ if and only if $n$ is an odd prime.
- Thomas Ordowski, Jun 08 2017
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) :
    (n.Prime ∧ n ≠ 2) ↔ n ^ 2 ≡ 1 [MOD a n * (a n - 1)] := by
  sorry

end OeisA224
