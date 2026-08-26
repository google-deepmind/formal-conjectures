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
# Rowland-style prime-generating recurrence

The sequence is defined by $a(1) = 2$ and for $n \ge 2$:
$a(n) = a(n-1) + \gcd(n, a(n-1))$ if $n$ is even, and
$a(n) = a(n-1) + \gcd(n-2, a(n-1))$ if $n$ is odd.

*References:*
- [A166944](https://oeis.org/A166944)
- E. S. Rowland, "A natural prime-generating recurrence", *J. Integer Sequences* **11** (2008),
  Article 08.2.8.
- V. Shevelev, "An infinite set of generators of primes based on the Rowland idea and
  conjectures concerning twin primes", arXiv preprint
  [arXiv:0910.4676](https://arxiv.org/abs/0910.4676) [math.NT], 2009.-/

namespace OeisA166944

/-- Defining recurrence for $a(n)$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 2 =>
    let prev := a (n + 1)
    let idx := n + 2
    if idx % 2 = 0 then prev + Nat.gcd idx prev
    else prev + Nat.gcd (idx - 2) prev

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 9 := by decide

/-- The difference sequence $d(n) = a(n) - a(n-1)$ for $n \ge 2$. -/
def d (n : ℕ) : ℕ := a n - a (n - 1)

/-- A prime $p$ is the greater of a twin prime pair if $p$ and $p - 2$ are both prime. -/
def IsGreaterTwinPrime (p : ℕ) : Prop := p.Prime ∧ (p - 2).Prime

/--
A value $R$ is a difference record if there exists $n \ge 2$ such that $d(n) = R$ and $R$
is strictly larger than all previous differences $d(k)$ for $2 \le k < n$.-/
def IsDifferenceRecord (R : ℕ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ d n = R ∧ ∀ k : ℕ, 2 ≤ k → k < n → d k < R

/--
Conjecture: Every record of differences $a(n)-a(n-1)$ more than 5 is the greater of twin primes
(A006512).-/
@[category research open, AMS 11]
theorem conjecture (R : ℕ) (hR : 5 < R) (hrec : IsDifferenceRecord R) :
    IsGreaterTwinPrime R := by
  sorry

end OeisA166944
