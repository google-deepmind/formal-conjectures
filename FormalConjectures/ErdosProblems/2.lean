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
# Erdős Problem 2

*Reference:* [erdosproblems.com/2](https://www.erdosproblems.com/2)

Erdős asked whether the smallest modulus in a distinct covering system can be arbitrarily large.
Hough proved that the answer is no, and Balister, Bollobás, Morris, Sahasrabudhe, and Tiba later
gave a simpler proof with an improved explicit upper bound.
-/

namespace Erdos2

/--
A finite set of residue classes forms a distinct covering system if every modulus is at least
`2`, no two listed classes have the same modulus, and every integer lies in one of the classes.
-/
def IsDistinctCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  (∀ p ∈ S, 2 ≤ p.2) ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.2 ≠ q.2) ∧
      ∀ z : ℤ, ∃ p ∈ S, z % (p.2 : ℤ) = p.1 % (p.2 : ℤ)

/--
The smallest modulus appearing in a finite family of integer residue classes.
-/
noncomputable def minModulus (S : Finset (ℤ × ℕ)) : ℕ :=
  sInf {m : ℕ | ∃ a : ℤ, (a, m) ∈ S}

/--
Can the smallest modulus of a covering system be arbitrarily large?

This problem has a negative answer: there is a universal bound on the least modulus of any
distinct covering system.
-/
@[category research solved, AMS 11]
theorem erdos_2 :
    answer(False) ↔
      ∃ B : ℕ, ∀ S : Finset (ℤ × ℕ), IsDistinctCoveringSystem S → minModulus S ≤ B := by
  sorry

end Erdos2
