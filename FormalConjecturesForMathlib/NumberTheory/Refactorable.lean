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

public import Mathlib.NumberTheory.Divisors

@[expose] public section

/-!
# Refactorable numbers

A positive integer $n \ge 1$ is *refactorable* (or a *$\tau$-number*, OEIS A033950) when its
divisor count `n.divisors.card` divides $n$.

*References:*
- [Wikipedia, Refactorable number](https://en.wikipedia.org/wiki/Refactorable_number)
- [OEIS A033950](https://oeis.org/A033950)
-/

namespace Nat

/-- A positive integer $n \ge 1$ is refactorable when `n.divisors.card` divides $n$. The bound
`1 ≤ n` excludes `n = 0`, where Mathlib sets `(0 : ℕ).divisors = ∅` and `0 ∣ 0` holds. -/
def IsRefactorable (n : ℕ) : Prop :=
  1 ≤ n ∧ n.divisors.card ∣ n

instance instDecidablePredIsRefactorable : DecidablePred IsRefactorable :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

@[simp]
theorem not_isRefactorable_zero : ¬ IsRefactorable 0 := by
  decide

@[simp]
theorem isRefactorable_one : IsRefactorable 1 := by
  decide

@[simp]
theorem isRefactorable_two : IsRefactorable 2 := by
  decide

theorem IsRefactorable.pos {n : ℕ} (h : n.IsRefactorable) : 0 < n :=
  h.1

end Nat
