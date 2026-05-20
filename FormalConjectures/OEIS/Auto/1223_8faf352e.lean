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

open Nat

/--
A001223: Prime gaps: differences between consecutive primes.
The $n$-th term of the sequence, $a(n)$, is the difference between the $(n+1)$-th prime and the $n$-th prime (using 1-based indexing for primes $p_k$).
$$a(n) = p_{n+1} - p_n$$
This corresponds to the difference between the $n$-th and $(n-1)$-th prime in Mathlib's 0-indexed sequence of primes.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (Nat.nth Nat.Prime n) - (Nat.nth Nat.Prime (n - 1))

-- Helper definition for extracting a finite subsequence (pattern) as a list
noncomputable def gap_subsequence (start_index : ℕ) (length : ℕ) : List ℕ :=
  (List.range length).map (fun i => a (start_index + i))

theorem a_one : a 1 = 1 := by
  simp_all[a]

theorem a_two : a 2 = 2 := by
  norm_num[a ·]

theorem a_three : a 3 = 2 := by
  norm_num[a]

theorem a_four : a 4 = 4 := by
  simp_all[a]

/--
oeis_1223_conjecture_4: Since (6a, 6b) is an admissible pattern of gaps for any integers a, b > 0
(and also if other multiples of 6 are inserted in between), the above conjecture follows from the
prime k-tuple conjecture which states that any admissible pattern occurs infinitely often (see, e.g.,
the Caldwell link). This also means that any subsequence a(n .. n+m) with n > 2 (as to exclude the
untypical primes 2 and 3) should occur infinitely many times at other starting points n'.
-/
theorem prime_gap_subsequences_occur_infinitely_often :
  ∀ (n : ℕ) (m : ℕ),
    n ≥ 3 →
    Set.Infinite {k : ℕ | gap_subsequence k (m + 1) = gap_subsequence n (m + 1)} :=
by sorry
