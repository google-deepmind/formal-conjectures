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

import FormalConjectures.Util.ProblemImports

/-!
# Fibonacci-Collatz sequence

Fibonacci-Collatz sequence: $a(1)=1, a(2)=2$; for $n > 2$, let $\mathrm{fib} = a(n-1) + a(n-2)$; if $\mathrm{fib}$ is odd then $a(n) = 3 \cdot \mathrm{fib} + 1$ else $a(n) = \mathrm{fib}/2$.

*References:*
- [A105801](https://oeis.org/A105801)
-/

namespace OeisA105801

/-- The primary defining sequence `a`.
$a(n)$ is the Fibonacci-Collatz sequence: $a(1)=1, a(2)=2$; for $n > 2$, let $\mathrm{fib} = a(n-1) + a(n-2)$; if $\mathrm{fib}$ is odd then $a(n) = 3 \cdot \mathrm{fib} + 1$ else $a(n) = \mathrm{fib}/2$. -/
def a : ℕ → ℕ
  | 0 => 0 -- The sequence is 1-indexed, a(0) is a conventional filler.
  | 1 => 1
  | 2 => 2
  | n + 3 =>
    let fib := a (n + 2) + a (n + 1)
    if fib % 2 = 1 then 3 * fib + 1 else fib / 2

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 10 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 6 := by decide

@[category test, AMS 11]
lemma test_a_5 : a 5 = 8 := by decide

/-- Conjecture: for every $k > 0$ there is an index $m$ such that all the $a(n)$ with $n > m$ have the same residue $\bmod 3^k$. -/
@[category research open, AMS 11]
theorem main_conjecture :
    ∀ k : ℕ, 0 < k → ∃ m : ℕ, ∀ n : ℕ, m < n → a n ≡ a (m + 1) [MOD (3^k)] := by
  sorry

end OeisA105801
