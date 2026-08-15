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

open Nat Finset Classical

/--
A352965: A variant of Van Eck's sequence where we only consider prime numbers:
for $n \ge 0$, if $a(n) = a(n-p)$ for some prime number $p$, take the least such $p$ and set $a(n+1) = p$;
otherwise $a(n+1) = 0$. Start with $a(1) = 0$.
We define $A(n)$ as the $n$-th term, $n \ge 1$.
-/
noncomputable def A352965 : ℕ → ℕ
| 0 => 0 -- Padding for 1-indexing implementation
| 1 => 0 -- A(1) = 0 by start condition.
| n + 1 => -- Calculates A(n+1). Let k = n.
  let k := n -- k is the index of the previous term A(k). k >= 1.

  -- The value of the previous term A(k)
  let a_k := A352965 k

  -- We seek the least prime p such that A(k) = A(k-p), where k-p >= 1, so p <= k - 1.
  -- Primes p must be in {2, 3, ..., k-1}. Finset.range k covers 0 to k-1.
  let all_lt_k := Finset.range k

  -- Filter for valid primes p that satisfy the condition.
  let S := all_lt_k.filter (fun p =>
    Nat.Prime p ∧ A352965 (k - p) = a_k)

  if h : S.Nonempty then
    S.min' h
  else
    0


theorem a_one : A352965 1 = 0 := by
  sorry

theorem a_two : A352965 2 = 0 := by
  sorry

theorem a_three : A352965 3 = 0 := by
  sorry

theorem a_four : A352965 4 = 2 := by
  sorry

/-- A352965 Will every prime number appear in the sequence? -/
theorem oeis_352965_conjecture_0 : ∀ (p : ℕ), Nat.Prime p → ∃ (n : ℕ), A352965 n = p := by sorry
