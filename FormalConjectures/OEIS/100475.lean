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
import Mathlib.Data.Nat.Prime.Nth

/-!
# Prime-th recurrence with reversal at each step

Prime-th recurrence with reversal at each step.
$$a(n) = \operatorname{reversal}(p_{a(n-1)})$$
with $a(0)=1$, where $p_k$ is the $k$-th prime number.

*References:* [A100475](https://oeis.org/A100475)
-/

namespace OeisA100475

open Nat List

/-- Reverses the base 10 digits of a natural number. -/
def reverseDigits (k : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 k |>.reverse)

/-- The primary defining sequence `a`.
a n is the Prime-th recurrence with reversal at each step.
$a(n) = \operatorname{reversal}(p_{a(n-1)})$
with $a(0)=1$, where $p_k$ is the $k$-th prime number (i.e., $p_1=2, p_2=3, \dots$). -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let k := a n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

@[category API, AMS 11]
lemma a_succ (n : ℕ) : a (n + 1) = if a n = 0 then 0 else reverseDigits (Nat.nth Nat.Prime (a n - 1)) := by
  rfl

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_1 : a 1 = 2 := by
  rw [a_succ]
  rw [test_a_0]
  simp [Nat.nth_prime_zero_eq_two, reverseDigits]

@[category test, AMS 11]
lemma test_a_2 : a 2 = 3 := by
  rw [a_succ]
  rw [test_a_1]
  simp [Nat.nth_prime_one_eq_three, reverseDigits]

@[category test, AMS 11]
lemma test_a_3 : a 3 = 5 := by
  rw [a_succ]
  rw [test_a_2]
  simp [Nat.nth_prime_two_eq_five, reverseDigits]

@[category test, AMS 11]
lemma test_a_4 : a 4 = 11 := by
  rw [a_succ]
  rw [test_a_3]
  simp [Nat.nth_prime_four_eq_eleven, reverseDigits]
  rfl

/-- Definition of the generalized sequence starting at x. -/
noncomputable def aStartAt (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 =>
    let k := aStartAt x n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

/-- A sequence $f : \mathbb{N} \to \mathbb{N}$ is ultimately periodic if there exist
$N, P \in \mathbb{N}$, with $P>0$, such that for all $n \ge N$, $f(n+P) = f(n)$. -/
def IsUltimatelyPeriodic (f : ℕ → ℕ) : Prop :=
  ∃ N P, P > 0 ∧ ∀ n, n ≥ N → f (n + P) = f n

/--
Starting at other than a(n) = 1, does this sequence ever go into a loop?
-/
@[category research open, AMS 11]
theorem main_conjecture (x : ℕ) (h : x ≠ 1) :
    IsUltimatelyPeriodic (aStartAt x) := by
  sorry

end OeisA100475
