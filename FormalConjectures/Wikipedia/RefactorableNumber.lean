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
# Refactorable Numbers

An integer $n \ge 1$ is called *refactorable* (or a *$\tau$-number*, OEIS A033950) when its divisor
count $d(n) = |\operatorname{divisors}(n)|$ divides $n$. Cooper and Kennedy (1990) introduced
$\tau$-numbers and proved their natural density vanishes; Simon Colton (1999) independently studied
them as refactorable numbers (see `FormalConjectures.OEIS.«111291»` for Colton's counting bound).
Joshua Zelinsky (2002) proved that three consecutive integers cannot all be refactorable. Both
Colton's question on infinitely many refactorable pairs $(n, n + 1)$ and Zelinsky's question on
refactorable integers in residue classes remain open.

*References:*
- [Wikipedia: Refactorable number](https://en.wikipedia.org/wiki/Refactorable_number)
- [OEIS A033950](https://oeis.org/A033950)
- C. N. Cooper and R. E. Kennedy (1990), *Int. J. Math. Math. Sci.*, vol. 13, 383–386.
- S. Colton (1999), *J. Integer Seq.* **2**, Art. 99.1.2.
- J. Zelinsky (2002), *J. Integer Seq.* **5**, Art. 02.2.8.
-/

@[expose] public section

namespace RefactorableNumber

/-- A positive integer $n \ge 1$ is refactorable when `n.divisors.card` divides $n$. The bound
`1 ≤ n` excludes $n = 0$, where Mathlib sets `(0 : ℕ).divisors = ∅` and `0 ∣ 0` holds. -/
def IsRefactorable (n : ℕ) : Prop :=
  1 ≤ n ∧ n.divisors.card ∣ n

/-- Both $8$ ($d(8) = 4 \mid 8$) and $9$ ($d(9) = 3 \mid 9$) are refactorable. -/
@[category test, AMS 11]
theorem isRefactorable_eight_and_nine : IsRefactorable 8 ∧ IsRefactorable 9 := by
  unfold IsRefactorable
  decide

/-- Neither $0$ nor $10$ ($d(10) = 4 \nmid 10$) is refactorable. -/
@[category test, AMS 11]
theorem not_isRefactorable_zero_and_ten : ¬ IsRefactorable 0 ∧ ¬ IsRefactorable 10 := by
  unfold IsRefactorable
  decide

/-- **Cooper–Kennedy Theorem (1990):** Refactorable integers have natural density $0$. -/
@[category research solved, AMS 11]
theorem refactorable_hasDensity_zero :
    {n : ℕ | IsRefactorable n}.HasDensity 0 := by
  sorry

/-- **Zelinsky's Theorem (2002):** Three consecutive integers cannot all be refactorable. -/
@[category research solved, AMS 11]
theorem no_three_consecutive_refactorable (n : ℕ) :
    ¬ (IsRefactorable n ∧ IsRefactorable (n + 1) ∧ IsRefactorable (n + 2)) := by
  sorry

/-- **Colton's Question (1999):** Are there infinitely many integers $n$ such that $n$ and $n + 1$
are simultaneously refactorable? -/
@[category research open, question, AMS 11]
theorem infinitely_many_consecutive_refactorable_pairs :
    {n : ℕ | IsRefactorable n ∧ IsRefactorable (n + 1)}.Infinite := by
  sorry

/-- **Zelinsky's Question (2002):** Given a modulus $m \ge 1$ and a refactorable integer
$n_0 \equiv a \pmod m$, must there exist a larger refactorable integer $n > n_0$ satisfying
$n \equiv a \pmod m$? -/
@[category research open, question, AMS 11]
theorem zelinsky_refactorable_progression_question :
    ∀ m a n₀ : ℕ, 1 ≤ m → IsRefactorable n₀ → n₀ ≡ a [MOD m] →
      ∃ n : ℕ, n₀ < n ∧ IsRefactorable n ∧ n ≡ a [MOD m] := by
  sorry

end RefactorableNumber
