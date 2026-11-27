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
count $d(n) = |\operatorname{divisors}(n)|$ divides $n$. Kennedy and Cooper (1990) introduced
$\tau$-numbers and proved their natural density vanishes; Simon Colton (1999) independently studied
them as refactorable numbers (see `FormalConjectures.OEIS.«111291»` for Colton's counting bound).
Joshua Zelinsky (2002) proved that three consecutive integers cannot all be refactorable. Both
Colton's conjecture on infinitely many refactorable pairs $(n, n + 1)$ and Zelinsky's conjecture on
refactorable integers in arithmetic progressions remain open.

*References:*
- [Wikipedia: Refactorable number](https://en.wikipedia.org/wiki/Refactorable_number)
- [OEIS A033950](https://oeis.org/A033950)
- R. E. Kennedy and C. N. Cooper (1990), *Int. J. Math. Math. Sci.* **13**(2), 383–386.
- S. Colton (1999), *J. Integer Seq.* **2**, Art. 99.1.2.
- J. Zelinsky (2002), *J. Integer Seq.* **5**, Art. 02.2.8.
-/

@[expose] public section

namespace RefactorableNumber

/-- Both $8$ ($d(8) = 4 \mid 8$) and $9$ ($d(9) = 3 \mid 9$) are refactorable. -/
@[category test, AMS 11]
theorem isRefactorable_eight_and_nine : Nat.IsRefactorable 8 ∧ Nat.IsRefactorable 9 := by
  decide

/-- Neither $0$ nor $10$ ($d(10) = 4 \nmid 10$) is refactorable. -/
@[category test, AMS 11]
theorem not_isRefactorable_zero_and_ten : ¬ Nat.IsRefactorable 0 ∧ ¬ Nat.IsRefactorable 10 := by
  decide

set_option linter.style.formal_proof_palomar false in
/-- **Kennedy–Cooper Theorem (1990):** Refactorable integers have natural density $0$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/ChironTheCentaur/rh-lab-refactorable-numbers/blob/1d1d800bc765379c544473134a2995db585d023b/RefactorableFC/Density.lean#L209"]
theorem refactorable_hasDensity_zero :
    {n : ℕ | n.IsRefactorable}.HasDensity 0 := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- **Zelinsky's Theorem (2002):** Three consecutive integers cannot all be refactorable. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/ChironTheCentaur/rh-lab-refactorable-numbers/blob/1d1d800bc765379c544473134a2995db585d023b/RefactorableFC/NoThreeFC.lean#L14"]
theorem no_three_consecutive_refactorable (n : ℕ) :
    ¬ (n.IsRefactorable ∧ (n + 1).IsRefactorable ∧ (n + 2).IsRefactorable) := by
  sorry

/-- **Colton's Conjecture (1999, Conjecture 2):** Infinitely many positive integers $n$ satisfy
both $n$ and $n + 1$ refactorable. -/
@[category research open, AMS 11]
theorem infinitely_many_consecutive_refactorable_pairs :
    {n : ℕ | n.IsRefactorable ∧ (n + 1).IsRefactorable}.Infinite := by
  sorry

/-- **Zelinsky's Conjecture (2002, Conjecture 32):** Every arithmetic progression of positive
integers containing a refactorable number contains infinitely many; equivalently, for every modulus
$m \ge 1$ and refactorable $n_0$, some refactorable $n > n_0$ satisfies $n \equiv n_0 \pmod m$. -/
@[category research open, AMS 11]
theorem zelinsky_refactorable_progression_conjecture :
    ∀ m n₀ : ℕ, 1 ≤ m → n₀.IsRefactorable →
      ∃ n : ℕ, n₀ < n ∧ n.IsRefactorable ∧ n ≡ n₀ [MOD m] := by
  sorry

end RefactorableNumber
