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


public import FormalConjecturesForMathlib.NumberTheory.AdditivelyComplete
public import Mathlib.NumberTheory.Divisors

@[expose] public section
/-!
# Practical numbers

A positive integer $n$ is called a *practical number* if every positive integer $m ≤ n$ can be
represented as a sum of distinct divisors of $n$.

*References*:
- [Wikipedia, Practical number](https://en.wikipedia.org/wiki/Practical_number)
- [OEIS A005153](https://oeis.org/A005153)

## Main definitions

* `Nat.IsPractical`: A natural number $n$ is practical if every positive integer $m ≤ n$ can be
  expressed as a sum of distinct divisors of $n$.
-/

namespace Nat

/-- A natural number $n$ is *practical* if every positive integer $m ≤ n$ can be represented
as a sum of distinct divisors of $n$. -/
def IsPractical (n : ℕ) : Prop :=
  ∀ m, m ≤ n → m ∈ subsetSums n.divisors

end Nat
