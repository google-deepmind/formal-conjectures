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

/-!
# Conjectures associated with A087719

Define $\varsigma(n)$ the smallest prime factor of $n$ (`Nat.minFac`). Let $a_n$ be the least
number such that the count of numbers $k \le a_n$ with $k > \varsigma(k)^n$ exceeds the count
of numbers with $k \le \varsigma(k)^n$.

The conjecture states that $a_n = 3^n + 3 \cdot 2^n + 6$ for $n \ge 1$.

*References:* [A087719](https://oeis.org/A087719)
-/

namespace OeisA87719

/-- Count of numbers k in {1, ..., m} where k > (minFac k)^n. -/
def countExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => k > k.minFac ^ n) |>.card

/-- Count of numbers k in {1, ..., m} where k ≤ (minFac k)^n. -/
def countNotExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => k ≤ k.minFac ^ n) |>.card

/-- There exists m such that countExceeding n m > countNotExceeding n m. -/
@[category undergraduate, AMS 11]
theorem a_exists (n : ℕ) : ∃ m, countExceeding n m > countNotExceeding n m := by
    sorry

/-- The sequence a(n): least m such that countExceeding n m > countNotExceeding n m. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.find (a_exists n)

/-- a(1) = 15. -/
@[category test, AMS 11]
theorem a_one : a 1 = 15 := by
  rw [a, Nat.find_eq_iff]
  refine ⟨by decide +native, ?_⟩
  intro m hm
  interval_cases m <;> decide +native

/-- a(2) = 27. -/
@[category test, AMS 11]
theorem a_two : a 2 = 27 := by
  rw [a, Nat.find_eq_iff]
  refine ⟨by decide +native, ?_⟩
  intro m hm
  interval_cases m <;> decide +native

/-- a(3) = 57. -/
@[category test, AMS 11]
theorem a_three : a 3 = 57 := by
  rw [a, Nat.find_eq_iff]
  refine ⟨by decide +native, ?_⟩
  intro m hm
  interval_cases m <;> decide +native

/-- Conjecture: a(n) = 3^n + 3 * 2^n + 6 for n ≥ 1. -/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/pull/1894/commits/7a286754f623759d69a3dd18f482c53c1d70959b", AMS 11]
theorem a_formula {n : ℕ} (hn : n ≥ 1) : a n = 3 ^ n + 3 * 2 ^ n + 6 := by
  sorry

end OeisA87719
