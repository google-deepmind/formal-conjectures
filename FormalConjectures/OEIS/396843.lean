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
# A compositional generating function

The ordinary generating function satisfies $A(xA(x)-3xA(x)^2)=x^2$,
with $A(0)=0$ and $a(1)=1$. Its coefficients form OEIS A396843.

*References:*
- [A396843](https://oeis.org/A396843), Paul D. Hanna, 2026.
- ElonSG / the-omega-institute/trureturing, [Earlier Lean proof](https://github.com/the-omega-institute/trureturing/pull/6773).
- [Li26] Wentao Li, [Integral construction and oddness](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/1cc54d7f3ecfdcea49625ce31c8df3e22d4c6146/proofs/independent-formalization/A396843/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA396843
open PowerSeries

/-- The normalized ordinary generating-function equation defining OEIS A396843. -/
def SourceEquation (A : PowerSeries ℤ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    A.subst (X * A - 3 * X * A ^ 2) = X ^ 2

/-- The normalized generating series of OEIS A396843. -/
noncomputable def series : PowerSeries ℤ := Classical.epsilon SourceEquation

/-- OEIS A396843, extended by $a(0)=0$ outside its offset-one domain. -/
noncomputable def a (n : ℕ) : ℤ := coeff n series

/-- The defining equation has a unique normalized integral solution; see [Li26]. -/
@[category API, AMS 11 13,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/1cc54d7f3ecfdcea49625ce31c8df3e22d4c6146/LeanOeisProofs/IndependentFormalization/A396843.lean#L508"]
theorem source_existence : ∃! A : PowerSeries ℤ, SourceEquation A := by
  sorry

/-- The selected series satisfies the defining equation and normalization. -/
@[category API, AMS 11 13]
theorem series_spec : SourceEquation series :=
  Classical.epsilon_spec source_existence.exists

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  simpa [a, coeff_zero_eq_constantCoeff] using series_spec.1

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := series_spec.2.1

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 15 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 117 := by
  sorry

@[category test, AMS 11]
theorem a_5 : a 5 = 975 := by
  sorry

/--
"Conjecture: all terms are odd."
- Paul D. Hanna, Jul 01 2026.

An earlier Lean parity proof appears in `the-omega-institute/trureturing` PR #6773.
Wentao Li's formalization also proves integral existence and uniqueness; see [Li26].
AI assistance was used for development and verification.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/1cc54d7f3ecfdcea49625ce31c8df3e22d4c6146/LeanOeisProofs/IndependentFormalization/A396843.lean#L531"]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : Odd (a n) := by
  sorry

end OeisA396843
