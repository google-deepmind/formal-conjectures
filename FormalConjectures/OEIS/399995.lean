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

module

public import FormalConjecturesUtil

/-!
# Weinstein's earlier-pair-counting sequence

Starting with $a(1)=0$, each term counts pairs of distinct earlier positions whose values
sum to the preceding term. Positions are counted separately even when their values agree.
We retain the official one-based indexing and extend the sequence by $a(0)=0$.

*References:*
- [A399995](https://oeis.org/A399995)
- [A397471](https://oeis.org/A397471)
- [Official term table](https://oeis.org/A399995/b399995.txt)
-/

@[expose] public section

namespace OeisA399995

/-- Count unordered pairs of distinct list positions whose values sum to the target. -/
def pairCount : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: xs, target =>
      xs.countP (fun y => x + y == target) + pairCount xs target

/-- The first $n+1$ official terms, obtained by appending one pair count at each step. -/
def prefixValues : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
      let xs := prefixValues n
      xs ++ [pairCount xs (xs.getLastD 0)]

/-- Weinstein's sequence with its official indexing and the extension $a(0)=0$. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (prefixValues n).getLastD 0

@[category test, AMS 5 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 5 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 5 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 5 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 5 11]
theorem a_5 : a 5 = 2 := by decide

@[category test, AMS 5 11]
theorem a_6 : a 6 = 4 := by decide

@[category test, AMS 5 11]
theorem a_7 : a 7 = 3 := by decide

@[category test, AMS 5 11]
theorem a_8 : a 8 = 4 := by decide

@[category test, AMS 5 11]
theorem a_9 : a 9 = 6 := by decide

/-- The value at zero is separate from the official one-based sequence. -/
@[category test, AMS 5 11]
theorem a_zero_extension : a 0 = 0 := by rfl

/-- The empty list has no pair of distinct positions. -/
@[category test, AMS 5 11]
theorem pair_count_nil (target : ℕ) : pairCount [] target = 0 := by rfl

/-- A position cannot be paired with itself. -/
@[category test, AMS 5 11]
theorem pair_count_singleton (x target : ℕ) : pairCount [x] target = 0 := by rfl

/-- Equal values at two distinct positions form a pair. -/
@[category test, AMS 5 11]
theorem pair_count_repeated_zero : pairCount [0, 0] 0 = 1 := by decide

/-- The two zero positions give different representations of one. -/
@[category test, AMS 5 11]
theorem pair_count_repeated_positions : pairCount [0, 0, 1] 1 = 2 := by decide

/-- No pair in this list sums to two. -/
@[category test, AMS 5 11]
theorem pair_count_missing_target : pairCount [0, 1] 2 = 0 := by decide

/-- Every generated prefix is nonempty and contains exactly its intended number of terms. -/
@[category API, AMS 5 11]
theorem prefix_values_length (n : ℕ) : (prefixValues n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prefixValues, ih]

/--
"Conjecture: Many numbers, beginning with 5 and 9, never occur in this sequence (see A397471)."
— [A399995](https://oeis.org/A399995).

In particular, $a(n)\ne5$ and $a(n)\ne9$ for every $n\ge1$.
-/
@[category research open, AMS 5 11]
theorem five_and_nine_never_occur :
    (∀ n : ℕ, 1 ≤ n → a n ≠ 5) ∧ (∀ n : ℕ, 1 ≤ n → a n ≠ 9) := by
  sorry

end OeisA399995
