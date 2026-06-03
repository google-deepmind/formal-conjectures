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
# Erdős Problem 768

*Reference:* [erdosproblems.com/768](https://www.erdosproblems.com/768)

Let `A ⊂ ℕ` be the set of `n` such that for every prime `p ∣ n` there exists
some divisor `d ∣ n`, `d > 1`, with `d ≡ 1 (mod p)`.  The question asks whether
`|A ∩ [1, N]| / N` has the form
`exp (-(c + o(1)) * sqrt (log N) * log log N)` for some `c > 0`.
-/

noncomputable section

namespace Erdos768

open Classical Filter Asymptotics

/--
The defining property of the set `A`: for every prime divisor `p` of `n`,
there is a nontrivial divisor `d` of `n` with `d ≡ 1 (mod p)`.
-/
def HasErdos768Property (n : ℕ) : Prop :=
  ∀ p : ℕ,
    Nat.Prime p →
      p ∣ n →
        ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ d % p = 1

/-- The counting function `|A ∩ [1, N]|`. -/
def erdos768Count (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter HasErdos768Property).card

/-- The normalized density `|A ∩ [1, N]| / N`. -/
def erdos768Density (N : ℕ) : ℝ :=
  (erdos768Count N : ℝ) / (N : ℝ)

/-- The scale `sqrt(log N) * log log N` appearing in the conjecture. -/
def erdos768Scale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ)) * Real.log (Real.log (N : ℝ))

/--
The asserted asymptotic
`|A ∩ [1, N]| / N = exp (-(c + o(1)) sqrt(log N) log log N)`.
-/
def Erdos768AsymptoticConjecture : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      ∃ error : ℕ → ℝ,
        error =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
          ∀ᶠ N in atTop,
            erdos768Density N =
              Real.exp (-(c + error N) * erdos768Scale N)

/--
Is there a constant `c > 0` such that
`|A ∩ [1, N]| / N = exp (-(c + o(1)) sqrt(log N) log log N)`?
-/
@[category research open, AMS 11]
theorem erdos_768 : answer(sorry) ↔ Erdos768AsymptoticConjecture := by
  sorry

end Erdos768

end

