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

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
# Prime divisors of the order of a group

* `Group.numPrimeDivisors G`: the number of distinct primes dividing `Nat.card G`;
* `Group.largestPrimeDivisor G`: the largest of them, or `0` if there is none.
-/

namespace Group

variable (G : Type*) [Group G]

/-- The number of distinct primes dividing the order of `G`. -/
noncomputable def numPrimeDivisors : ℕ := (Nat.card G).primeFactors.card

/-- The largest prime dividing the order of `G`, or `0` if there is none (`G` trivial or
infinite). -/
noncomputable def largestPrimeDivisor : ℕ := (Nat.card G).primeFactors.sup id


@[simp]
theorem numPrimeDivisors_of_subsingleton [Subsingleton G] : numPrimeDivisors G = 0 := by
  simp [numPrimeDivisors]

@[simp]
theorem largestPrimeDivisor_of_subsingleton [Subsingleton G] : largestPrimeDivisor G = 0 := by
  simp [largestPrimeDivisor]

end Group
