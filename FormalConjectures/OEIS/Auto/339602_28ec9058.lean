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
A030101: The number whose binary expansion is the reversal of the binary expansion of $n$.
This is computed by taking the list of digits of $n$ in base 2 (LSB first), reversing the list, and interpreting the result as a number.
-/
def A030101 (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (Nat.digits 2 n))

/--
A339602: $a(n) = (a(n-2) \oplus A030101(a(n-1))) + 1$, $a(0) = 0$, $a(1) = 1$.
-/
def a : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  -- For k = n + 2, the terms are a(n) and a(n + 1), where n < n + 2 and n + 1 < n + 2.
  | n + 2 => (a n).xor (A030101 (a (n + 1))) + 1
termination_by n => n


theorem a_zero : a 0 = 0 := by
  sorry

theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 2 := by
  sorry

theorem a_three : a 3 = 1 := by
  sorry

open Finset

/--
Conjecture: Let p be an odd number, then a(n) = p will be more frequently found in this sequence than a(n) = p+1.
This is formalized as: for any odd p, the count of p in the sequence up to index N eventually always exceeds the count of p+1.
-/
theorem oeis_339602_conjecture_1 (p : ℕ) (hp_odd : p % 2 = 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (filter (fun n : ℕ => a n = p) (range N)).card > (filter (fun n : ℕ => a n = p + 1) (range N)).card := by
  sorry
