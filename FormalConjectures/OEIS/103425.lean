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

import FormalConjecturesUtil

/-!
# Sequence A103425 contains infinitely many primes

A103425 is defined by the recurrence relation $a(n) = 3 a(n-1) + a(n-2) - 3 a(n-3)$
with initial terms $a(0)=1, a(1)=3, a(2)=5$. The conjecture states that this sequence
contains infinitely many primes.

*References:*
- [A103425](https://oeis.org/A103425)
-/

namespace OeisA103425

/--
The primary defining sequence `a`.
$a(n)$ is defined by the recurrence relation $a(n) = 3 a(n-1) + a(n-2) - 3 a(n-3)$
with initial terms $a(0)=1, a(1)=3, a(2)=5$.
-/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | n + 3 => 3 * a (n + 2) + a (n + 1) - 3 * a n

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
lemma test_a_1 : a 1 = 3 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 5 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 15 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 41 := by decide

def IsWeightedTribonacci (a b c : ℤ) (x : ℕ → ℤ) : Prop :=
  ∀ n, x (n + 3) = a * x (n + 2) + b * x (n + 1) + c * x n

/--
"The current sequence contains primes, including 3, 5, 41, 21523361. Is there an (a, b, c) weighted tribonacci sequence with a, b, c relatively prime which is prime-free?"
-/

@[category research open, AMS 11]
theorem main_conjecture : answer(sorry) ↔
    ∃ (a b c : ℤ) (x : ℕ → ℤ),
      Nat.gcd (Int.gcd a b) c.natAbs = 1 ∧
      IsWeightedTribonacci a b c x ∧
      ∀ n, ¬ (x n).natAbs.Prime := by
  sorry

end OeisA103425
