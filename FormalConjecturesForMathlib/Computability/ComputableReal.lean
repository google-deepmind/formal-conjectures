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

public import Mathlib.Computability.Partrec
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Data.Real.Basic

/-!
# Computable real numbers

A real number is *computable* if it can be approximated by a computable sequence of rationals
with an explicit error bound. This is the notion used to state that a construction of a real
number is effective, as opposed to a mere existence proof.

The `Primcodable ℚ` instance needed to speak of a computable sequence of rationals comes from
`Rat.instDenumerable` through `Primcodable.ofDenumerable`.

*References:*
- [Wikipedia, Computable number](https://en.wikipedia.org/wiki/Computable_number)

## Main definitions

* `Real.IsComputable`: a real number is the limit of a computable sequence of rationals with
  error at most `1 / (n + 1)` at step `n`.
-/

@[expose] public section

namespace Real

/-- A real number `x` is *computable* if there is a computable sequence of rationals `f` with
`|x - f n| ≤ 1 / (n + 1)` for every `n`. The rate `1 / (n + 1)` is a normalisation: any
computable sequence of rationals converging to `x` at a computable rate can be reindexed to
satisfy it. -/
def IsComputable (x : ℝ) : Prop :=
  ∃ f : ℕ → ℚ, Computable f ∧ ∀ n : ℕ, |x - f n| ≤ 1 / (n + 1)

/-- Every rational number is computable, witnessed by the constant sequence. -/
theorem isComputable_ratCast (q : ℚ) : IsComputable (q : ℝ) :=
  ⟨fun _ => q, Computable.const q, fun n => by
    simp only [sub_self, abs_zero]
    exact (one_div_pos.2 (Nat.cast_add_one_pos n)).le⟩

end Real
