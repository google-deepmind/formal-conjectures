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

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Real.Archimedean

@[expose] public section
/-!
# Mahler's Z-numbers

A *Z-number* is a positive real number `ξ` such that the fractional part of
`ξ (3/2)^n` lies in `[0, 1/2)` for every positive integer `n`. Mahler asked
whether any Z-number exists; this is still open.

*References*:
- [Mah68] Mahler, Kurt. "An unsolved problem on the powers of 3/2."
  Journal of the Australian Mathematical Society 8.2 (1968): 313-321.
- [Wikipedia, Mahler's 3/2 problem](https://en.wikipedia.org/wiki/Mahler%27s_3/2_problem)

## Main definitions

* `IsZNumber`: a real number is a Z-number.
-/

/-- A **Z-number** is a positive real number `ξ` such that the fractional part of
`ξ (3/2)^n` lies in `[0, 1/2)` for every positive integer `n`. -/
def IsZNumber (ξ : ℝ) : Prop :=
  0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → Int.fract (ξ * (3 / 2 : ℝ) ^ n) < 1 / 2
