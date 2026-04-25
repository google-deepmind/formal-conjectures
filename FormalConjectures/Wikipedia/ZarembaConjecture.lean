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

/-!
# Zaremba's conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Zaremba%27s_conjecture)
-/

namespace ZarembaConjecture

/--
The finite list of partial quotients in the simple continued fraction expansion of `a / d`,
excluding the initial integer part. This is computed by the Euclidean algorithm:
for `0 < a < d`, the first quotient is `d / a`, and the process continues with
`(d % a) / a`.
-/
def partialQuotients : ℕ → ℕ → List ℕ
  | 0, _ => []
  | a + 1, d => d / (a + 1) :: partialQuotients (d % (a + 1)) (a + 1)
termination_by a _ => a
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

#eval partialQuotients 333 106

/-- The finset of partial quotients appearing in the continued fraction expansion of `a / d`. -/
def partialQuotientFinset (a d : ℕ) : Finset ℕ :=
  (partialQuotients a d).toFinset

/-- The maximum partial quotient of `a / d`, as a `WithBot ℕ` so that `a = 0` gives `⊥`. -/
def maxPartialQuotient (a d : ℕ) : WithBot ℕ :=
  (partialQuotientFinset a d).max

/-- Boolean check that all partial quotients of `a / d` are at most `A`. -/
def partialQuotientsBoundedBy (A a d : ℕ) : Bool :=
  (partialQuotients a d).all fun q => q ≤ A

/-- All partial quotients of `a / d` are at most `A`. -/
def PartialQuotientsBoundedBy (A a d : ℕ) : Prop :=
  partialQuotientsBoundedBy A a d = true

/--
The numerators `a < d` that are coprime to `d` and whose partial quotients for `a / d`
are all at most `A`.
-/
def candidateNumerators (A d : ℕ) : Finset ℕ :=
  (Finset.range d).filter fun a =>
    decide (0 < a) && decide (Nat.gcd a d = 1) && partialQuotientsBoundedBy A a d

/-- For $5/6 = [0; 1, 5]$, the partial quotients are `1` and `5`. -/
@[category test, AMS 11]
theorem partialQuotientFinset_five_six :
    partialQuotientFinset 5 6 = ({1, 5} : Finset ℕ) := by
  native_decide

/-- The maximum partial quotient of $5/6$ is `5`. -/
@[category test, AMS 11]
theorem maxPartialQuotient_five_six :
    maxPartialQuotient 5 6 = (5 : WithBot ℕ) := by
  native_decide

/-- The bound `A = 4` already fails for denominator `6`. -/
@[category test, AMS 11]
theorem four_fails_at_six :
    candidateNumerators 4 6 = ∅ := by
  native_decide

/--
Zaremba's conjecture: there is an absolute constant $A$ such that for every denominator
$d > 1$, there is a numerator $a$ coprime to $d$, with $0 < a < d$, for which every partial
quotient in the continued fraction of $a/d$ is at most $A$.
-/
@[category research open, AMS 11]
theorem zaremba_conjecture :
    ∃ A : ℕ, 0 < A ∧ ∀ d : ℕ, 1 < d →
      ∃ a : ℕ, 0 < a ∧ a < d ∧ Nat.Coprime a d ∧
        ∀ n : ℕ, ∀ b : ℝ,
          (GenContFract.of ((a : ℝ) / (d : ℝ))).partDens.get? n = some b → b ≤ A := by
  sorry

end ZarembaConjecture
