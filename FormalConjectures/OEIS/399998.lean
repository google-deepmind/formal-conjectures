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
# Cestnik's nested recurrence

The recurrence starts at $a(0)=0$ and sets
$a(n+1)=a(n-a(a(n))^2)+1$. Each new term is one more than an earlier term.
The references form a rooted tree in which the value of a term is its depth.

*References:*
- [A399998](https://oeis.org/A399998)
- [Official term table](https://oeis.org/A399998/b399998.txt)
-/

@[expose] public section

namespace OeisA399998

/-- Compute the next term only when both lookups and the nonnegative index are valid. -/
def nextTerm (xs : List ℕ) : Option ℕ := do
  let current ← xs.getLast?
  let inner ← xs[current]?
  let n := xs.length - 1
  if inner ^ 2 ≤ n then
    let earlier ← xs[n - inner ^ 2]?
    return earlier + 1
  else
    none

/-- Append one term when the recurrence's lookup conditions are satisfied. -/
def extend (xs : List ℕ) : Option (List ℕ) :=
  (nextTerm xs).map fun value => xs ++ [value]

/-- The prefix at index $n$, or `none` if a required transition fails. -/
def prefixValues : ℕ → Option (List ℕ)
  | 0 => some [0]
  | n + 1 => (prefixValues n).bind extend

/-- The official zero-based term, provided every transition through this index succeeds. -/
def a (n : ℕ) : Option ℕ := (prefixValues n).bind List.getLast?

@[category test, AMS 11]
theorem a_0 : a 0 = some 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = some 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = some 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = some 2 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = some 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = some 3 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = some 2 := by decide

@[category test, AMS 11]
theorem a_7 : a 7 = some 4 := by decide

@[category test, AMS 11]
theorem a_8 : a 8 = some 3 := by decide

/-- An empty prefix cannot supply a current term. -/
@[category test, AMS 11]
theorem empty_prefix_rejected : nextTerm [] = none := by decide

/-- An unavailable inner index is rejected. -/
@[category test, AMS 11]
theorem unavailable_inner_index_rejected : nextTerm [1] = none := by decide

/-- The square guard rejects an outer index that would be negative. -/
@[category test, AMS 11]
theorem negative_outer_index_rejected : nextTerm [0, 2, 2] = none := by decide

/-- Equality in the square guard allows a lookup at index zero. -/
@[category test, AMS 11]
theorem zero_outer_index_accepted : nextTerm [1, 0] = some 2 := by decide

/-- A zero square allows a lookup at the last available index. -/
@[category test, AMS 11]
theorem last_outer_index_accepted : nextTerm [0, 0, 0] = some 1 := by decide

/-- A successful transition appends exactly one term. -/
@[category API, AMS 11]
theorem extend_length {xs ys : List ℕ} (h : extend xs = some ys) :
    ys.length = xs.length + 1 := by
  cases hnext : nextTerm xs with
  | none => simp [extend, hnext] at h
  | some value =>
      simp [extend, hnext] at h
      rw [← h]
      simp

/-- A successful prefix contains the terms at indices $0$ through $n$. -/
@[category API, AMS 11]
theorem prefix_values_length {n : ℕ} {xs : List ℕ} (h : prefixValues n = some xs) :
    xs.length = n + 1 := by
  induction n generalizing xs with
  | zero =>
      simp only [prefixValues, Option.some.injEq] at h
      rw [← h]
      rfl
  | succ n ih =>
      cases hprev : prefixValues n with
      | none => simp [prefixValues, hprev] at h
      | some ys =>
          have hnext : extend ys = some xs := by simpa [prefixValues, hprev] using h
          rw [extend_length hnext, ih hprev]

/-- A failed prefix cannot become successful at the next index. -/
@[category API, AMS 11]
theorem prefix_values_failure_persists {n : ℕ} (h : prefixValues n = none) :
    prefixValues (n + 1) = none := by
  simp [prefixValues, h]

/--
"a(n) ~ 2^(1/4)*n^(1/2) (conjectured)."
— [A399998](https://oeis.org/A399998).

The recurrence is defined for every $n\ge0$, with $a(n)\sim2^{1/4}\sqrt n$.
-/
@[category research open, AMS 11 40]
theorem total_and_asymptotic :
    (∀ n : ℕ, ∃ value : ℕ, a n = some value) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
        ∀ n : ℕ, N ≤ n → ∀ value : ℕ, a n = some value →
          |(value : ℝ) / ((2 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (n : ℝ)) - 1| < ε := by
  sorry

end OeisA399998
