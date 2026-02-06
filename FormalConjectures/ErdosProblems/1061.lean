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
# Erdős Problem 1061

*References:*
 - [erdosproblems.com/1061](https://www.erdosproblems.com/1061)
 - [Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004), Problem B15.
-/

open Filter Asymptotics
open scoped ArithmeticFunction.sigma

namespace Erdos1061

/-- Let `S x` count the number of **ordered** pairs of positive integers `(a, b)` with `a + b ≤ x`
such that `σ(a) + σ(b) = σ(a + b)`, where `σ` is the sum of divisors function.

In particular, `(a, b)` and `(b, a)` are counted separately; an unordered variant could be obtained
by additionally requiring `a ≤ b`. -/
noncomputable abbrev S (x : ℝ) : ℝ :=
  ((Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
      a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b)).card

/--
How many (ordered) solutions are there to `σ(a) + σ(b) = σ(a + b)` with `a + b ≤ x`?
Is it true that this number is asymptotic to `c * x` for some constant `c > 0`?
-/
@[category research open, AMS 11]
theorem erdos_1061 : answer(sorry) ↔ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ ↦ c * x) := by
  sorry

end Erdos1061
