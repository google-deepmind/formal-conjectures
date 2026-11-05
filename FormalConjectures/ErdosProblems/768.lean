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

Let `A ⊆ ℕ` be the set of `n` such that for every prime `p ∣ n` there is a
divisor `d ∣ n` with `d > 1` and `d ≡ 1 (mod p)`. Is it true that there is a
constant `c > 0` such that
`|A ∩ [1,N]| / N = exp(-(c + o(1)) √(log N) · log log N)`?

Note that 1 ∈ A vacuously, and that the condition d > 1 is essential: with d = 1 permitted the condition would hold for every n (the number of Sylow p-subgroups of a nonabelian finite simple group is ≡ 1 (mod p) and ≠ 1).

Resolved by Li [Li26]: the limit exists and equals `1/(2√(log 2))`.
The proof was formalised in Lean by Li using Aristotle (Harmonic); the
definitions below match the proof repository verbatim.

[Li26] Li, E., _The Sylow Divisor Condition: a Resolution of Erdős
Problem 768_. [arXiv:2606.24872](https://arxiv.org/abs/2606.24872)
-/

open Filter

open scoped Classical

namespace Erdos768

/-- `n` satisfies the **Sylow divisor condition** if for every prime `p ∣ n`
there is a divisor `d ∣ n` with `d > 1` and `d ≡ 1 (mod p)`. Note that `1`
satisfies the condition vacuously. -/
def SylowDivisor (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ d % p = 1

/-- `Acount x = #{n ≤ x : n satisfies the Sylow divisor condition}`. -/
noncomputable def Acount (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter SylowDivisor).card

/-- Is there a constant `c > 0` such that
`A(x)/x = exp(-(c + o(1)) √(log x) · log log x)`, i.e. such that
`log(x / A(x)) / (√(log x) · log log x) → c`?

Resolved affirmatively by Li [Li26], with `c = 1/(2√(log 2))`. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/ericlisg/erdos768-lean/blob/v1.0.0/RequestProject/Main.lean"]
theorem erdos_768 : answer(True) ↔ ∃ c : ℝ, 0 < c ∧
    Tendsto (fun x : ℝ =>
        Real.log (x / (Acount x : ℝ)) /
          (Real.sqrt (Real.log x) * Real.log (Real.log x)))
      atTop (nhds c) := by
  sorry

/-- The explicit constant (Theorem 1.1 of [Li26]):
`log(x / A(x)) / (√(log x) · log log x) → 1/(2√(log 2))`.
This is verbatim the statement proved as `Erdos768.erdos_768` in the linked
repository. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/ericlisg/erdos768-lean/blob/v1.0.0/RequestProject/Main.lean"]
theorem erdos_768.variants.explicit_constant :
    Tendsto (fun x : ℝ =>
        Real.log (x / (Acount x : ℝ)) /
          (Real.sqrt (Real.log x) * Real.log (Real.log x)))
      atTop (nhds (1 / (2 * Real.sqrt (Real.log 2)))) := by
  sorry

end Erdos768
