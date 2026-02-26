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
# Lychrel numbers in base 10

A (base-10) *Lychrel number* is a positive integer which never becomes a palindrome under the
iteration

$$a_{0} = n, \qquad a_{k+1} = a_k + \operatorname{rev}_{10}(a_k).$$

The main conjecture asserts that there are no Lychrel numbers in base 10.

*References:*
* [Wikipedia: Lychrel number](https://en.wikipedia.org/wiki/Lychrel_number)
* [MathWorld: Lychrel Number](https://mathworld.wolfram.com/LychrelNumber.html)
* [OEIS A023108](https://oeis.org/A023108)
* [OEIS A023109](https://oeis.org/A023109)
-/

namespace LychrelNumbers

/-- The base (10) used for digit reversal. -/
abbrev base : ℕ := 10

/--
The digit-reversal map $\operatorname{rev}_{10}(n)$.

Implementation note: `Nat.digits base n` returns the digits of `n` in *little-endian* order.
Reversing this list and interpreting it again as little-endian digits gives the usual digit
reversal.
-/
def rev10 (n : ℕ) : ℕ :=
  Nat.ofDigits base (Nat.digits base n).reverse

/-- A number is a (base-10) palindrome if it equals its digit reversal. -/
def IsPalindrome10 (n : ℕ) : Prop :=
  rev10 n = n

/-- One step of the Lychrel iteration: `n ↦ n + rev10 n`. -/
def lychrelStep (n : ℕ) : ℕ :=
  n + rev10 n

/-- The `k`-th iterate of the Lychrel step, starting from `n`. -/
def lychrelIter (n k : ℕ) : ℕ :=
  Nat.rec n (fun _ acc ↦ lychrelStep acc) k

/-- `n` is a (base-10) Lychrel number if no iterate of the Lychrel process is a palindrome. -/
def IsLychrel10 (n : ℕ) : Prop :=
  ∀ k : ℕ, ¬ IsPalindrome10 (lychrelIter n k)

/--
**Lychrel conjecture (base 10):** there are no Lychrel numbers in base 10.

Equivalently, every positive integer eventually becomes a palindrome under the Lychrel iteration.
-/
@[category research open, AMS 11]
theorem no_lychrel_numbers_base10 : ∀ n : ℕ, 0 < n → ¬ IsLychrel10 n := by
  sorry

/-- An equivalent formulation of `no_lychrel_numbers_base10`. -/
@[category API, AMS 11]
theorem eventually_palindrome_base10 :
    (∀ n : ℕ, 0 < n → ∃ k : ℕ, IsPalindrome10 (lychrelIter n k)) ↔
      (∀ n : ℕ, 0 < n → ¬ IsLychrel10 n) := by
  constructor
  · intro h n hn hn_lychrel
    rcases h n hn with ⟨k, hk⟩
    exact hn_lychrel k hk
  · intro h n hn
    by_contra hcontra
    have : IsLychrel10 n := by
      intro k hk
      exact hcontra ⟨k, hk⟩
    exact h n hn this


/-- Sanity check: digit reversal of `120` is `21`. -/
@[category test, AMS 11]
theorem rev10_120 : rev10 120 = 21 := by
  native_decide

/-- Sanity check: `121` is a base-10 palindrome. -/
@[category test, AMS 11]
theorem palindrome_121 : IsPalindrome10 121 := by
  dsimp [IsPalindrome10]
  native_decide

/-- Sanity check: `56 → 121` in one Lychrel step. -/
@[category test, AMS 11]
theorem lychrelIter_56_one : lychrelIter 56 1 = 121 := by
  native_decide

/-- Sanity check: the Lychrel iteration at `56` reaches a palindrome. -/
@[category test, AMS 11]
theorem eventually_palindrome_56 : ∃ k : ℕ, IsPalindrome10 (lychrelIter 56 k) := by
  refine ⟨1, ?_⟩
  dsimp [IsPalindrome10]
  native_decide
end LychrelNumbers
