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


public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# Exact prefixes of the factorial-gap series

Definitions used in arithmetic reformulations of Erdős Problem 68.

Both are exactly computable over `ℚ` and `ℤ`, so the reformulation they
support can be evaluated at any index without any real-number reasoning.
-/

namespace Erdos68

/-- The exact rational prefix `∑ k ∈ {2, …, n}, 1 / (k! - 1)` of the
factorial-gap series. -/
def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

/-- The first integer strictly greater than `n! * x`. -/
def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

end Erdos68
