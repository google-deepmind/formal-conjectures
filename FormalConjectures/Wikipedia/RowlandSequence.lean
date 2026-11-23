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
# Rowland's GCD prime-generating recurrence

Define $a(1) = 7$ and $a(n) = a(n - 1) + \gcd(n, a(n - 1))$ for $n \ge 2$ (`OEIS A106108`), with
step increments $d(n) = a(n) - a(n - 1) = \gcd(n, a(n - 1))$ (`OEIS A132199` lists $d(n + 1)$ for
$n \ge 1$). Eric S. Rowland established in 2008 that every $d(n)$ with $n \ge 2$ equals $1$ or an
odd prime, and conjectured that every odd prime arises as $d(n)$ for some $n \ge 2$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Formula_for_primes#Rowland%27s_prime-generating_sequence)
- [OEIS A106108](https://oeis.org/A106108)
- [OEIS A132199](https://oeis.org/A132199)
- E. S. Rowland, *A natural prime-generating recurrence*, J. Integer Seq. **11** (2008),
  Article 08.2.8.
-/

@[expose] public section

namespace RowlandSequence

/-- Rowland's sequence (`OEIS A106108`), starting at $a(1) = 7$ with recurrence
$a(n) = a(n - 1) + \gcd(n, a(n - 1))$ for $n \ge 2$ (and $a(0) = 0$). -/
def rowlandSeq : ℕ → ℕ
  | 0 => 0
  | 1 => 7
  | n + 2 =>
    let prev := rowlandSeq (n + 1)
    prev + Nat.gcd (n + 2) prev

/-- Step increment $d(n) = a(n) - a(n - 1)$ of `rowlandSeq` (meaningful for $n \ge 2$; shifted by
one from `OEIS A132199`, where `A132199(n) = rowlandDiff (n + 1)`). -/
def rowlandDiff (n : ℕ) : ℕ :=
  rowlandSeq n - rowlandSeq (n - 1)

/-- Checks the initial values $a(1), \dots, a(6) = 7, 8, 9, 10, 15, 18$ of `rowlandSeq`. -/
@[category test, AMS 11]
theorem rowlandSeq_initial_values :
    rowlandSeq 1 = 7 ∧ rowlandSeq 2 = 8 ∧ rowlandSeq 3 = 9 ∧
      rowlandSeq 4 = 10 ∧ rowlandSeq 5 = 15 ∧ rowlandSeq 6 = 18 := by
  decide

/-- Checks $d(2) = 1$ alongside the odd-prime increments $d(5) = 5$, $d(6) = 3$, and
$d(11) = 11$. -/
@[category test, AMS 11]
theorem rowlandDiff_small_witnesses :
    rowlandDiff 2 = 1 ∧ rowlandDiff 5 = 5 ∧ rowlandDiff 6 = 3 ∧ rowlandDiff 11 = 11 := by
  decide

/--
Rowland's theorem (2008): for every $n \ge 2$, the step $d(n) = a(n) - a(n - 1)$ equals $1$ or is
prime.
-/
@[category research solved, AMS 11]
theorem rowland_diff_eq_one_or_prime {n : ℕ} (hn : 2 ≤ n) :
    rowlandDiff n = 1 ∨ (rowlandDiff n).Prime := by
  sorry

/--
Rowland's conjecture (2008): every odd prime $p$ occurs as $d(n) = a(n) - a(n - 1)$ at some index
$n \ge 2$. The prime $2$ is excluded because $n$ and $a(n - 1)$ always have opposite parity, and
$n \ge 2$ excludes the artifact `rowlandDiff 1 = 7`.
-/
@[category research open, AMS 11]
theorem rowland_generates_all_odd_primes {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ∃ n : ℕ, 2 ≤ n ∧ rowlandDiff n = p := by
  sorry

end RowlandSequence
