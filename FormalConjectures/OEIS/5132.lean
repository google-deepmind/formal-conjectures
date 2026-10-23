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
# Recamán's sequence

Start with $a(0)=0$. At step $n>0$, subtract $n$ from the preceding term when the result is
nonnegative and has not appeared earlier; otherwise add $n$.

*References:*
- [OEIS A005132](https://oeis.org/A005132)
-/

@[expose] public section

namespace OeisA5132

/--
Choose the next Recamán value from a finite history and a step size: use the positive unseen
subtraction candidate when possible, and the addition candidate otherwise.
-/
def nextTerm (previous : List ℕ) (step : ℕ) : ℕ :=
  let current := previous.getLastD 0
  if step < current ∧ current - step ∉ previous then current - step else current + step

/-- The complete list $[a(0),\ldots,a(n)]$ of Recamán values through index $n$. -/
def sequencePrefix : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
      let previous := sequencePrefix n
      previous ++ [nextTerm previous (n + 1)]

/-- The finite prefix through index $n$ has exactly $n+1$ entries. -/
@[simp, category API, AMS 11]
theorem prefix_length : ∀ n, (sequencePrefix n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [sequencePrefix, prefix_length n]

/-- Zero remains in every generated prefix. -/
@[simp, category API, AMS 11]
theorem zero_mem_prefix : ∀ n, 0 ∈ sequencePrefix n
  | 0 => by simp [sequencePrefix]
  | n + 1 => by simp [sequencePrefix, zero_mem_prefix n]

/-- Recamán's sequence value at index $n$, read from the end of its complete finite prefix. -/
def a (n : ℕ) : ℕ :=
  (sequencePrefix n).getLastD 0

/-- The OEIS nonnegative subtraction condition is equivalent to the strict-positive version used
by `nextTerm`, because a zero candidate has already appeared in every prefix. -/
@[category API, AMS 11]
theorem subtraction_condition_iff (n : ℕ) :
    (n + 1 ≤ a n ∧ a n - (n + 1) ∉ sequencePrefix n) ↔
      (n + 1 < a n ∧ a n - (n + 1) ∉ sequencePrefix n) := by
  constructor
  · rintro ⟨hle, hunseen⟩
    refine ⟨?_, hunseen⟩
    by_contra hlt
    have hzero : a n - (n + 1) = 0 := by omega
    apply hunseen
    rw [hzero]
    exact zero_mem_prefix n
  · rintro ⟨hlt, hunseen⟩
    exact ⟨by omega, hunseen⟩

/-- The prefix at the next index is obtained by appending exactly one recurrence step. -/
@[simp, category API, AMS 11]
theorem prefix_succ (n : ℕ) :
    sequencePrefix (n + 1) =
      sequencePrefix n ++ [nextTerm (sequencePrefix n) (n + 1)] := by
  rfl

/--
The public sequence satisfies the defining Recamán recurrence, including its positive and unseen
subtraction conditions.
-/
@[simp, category API, AMS 11]
theorem a_succ (n : ℕ) :
    a (n + 1) =
      if n + 1 < a n ∧ a n - (n + 1) ∉ sequencePrefix n then
        a n - (n + 1)
      else
        a n + (n + 1) := by
  simp [a, sequencePrefix, nextTerm]

/-- The public recurrence in the exact nonnegative-subtraction grammar used by OEIS. -/
@[category API, AMS 11]
theorem a_succ_oeis (n : ℕ) :
    a (n + 1) =
      if n + 1 ≤ a n ∧ a n - (n + 1) ∉ sequencePrefix n then
        a n - (n + 1)
      else
        a n + (n + 1) := by
  simpa only [subtraction_condition_iff] using a_succ n

/-- The current sequence value occurs in the complete prefix through its index. -/
@[category API, AMS 11]
theorem a_mem_prefix (n : ℕ) : a n ∈ sequencePrefix n := by
  cases n with
  | zero => simp [a, sequencePrefix]
  | succ n => simp [a, sequencePrefix, nextTerm]

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 6 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 7 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 13 := by decide

/-- The value at index $20$ is $42$, which is repeated later. -/
@[category test, AMS 11]
theorem a_20 : a 20 = 42 := by
  set_option maxRecDepth 100000 in
    decide

/-- The value $42$ occurs again at index $24$. -/
@[category test, AMS 11]
theorem a_24 : a 24 = 42 := by
  set_option maxRecDepth 100000 in
    decide

/-- Recamán's sequence is not injective: its entries at indices $20$ and $24$ are both $42$. -/
@[category test, AMS 11]
theorem not_injective : ¬ Function.Injective a := by
  intro h
  have : (20 : ℕ) = 24 := h (a_20.trans a_24.symm)
  omega

/--
“I conjecture that every number eventually appears” — N. J. A. Sloane,
[OEIS A005132](https://oeis.org/A005132).

Sloane later added that he was no longer sure every number appears. The coverage question remains
open and is formalized here as surjectivity onto the natural numbers.
-/
@[category research open, AMS 11]
theorem conjecture : Function.Surjective a := by
  sorry

end OeisA5132
