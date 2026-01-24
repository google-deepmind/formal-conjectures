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
# Ben Green's Open Problem 6

*Reference:* [Ben Green's Open Problem 6](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.6)
-/

open scoped Pointwise

namespace Green6

/-- The d-dimensional box [N]^d, consisting of all d-tuples with coordinates in {1, ..., N}. -/
def boxPower (d N : ℕ) : Finset (Fin d → ℕ) :=
  Finset.univ.filter (fun f => ∀ i, f i ∈ Finset.Icc 1 N)

/--
Fix an integer $d$. What is the largest sum-free subset of $[N]^d$?

A sum-free set is one where the equation $x + y = z$ has no solution with $x, y, z$ in the set.
-/
@[category research open, AMS 11]
theorem green_6 :
    ∀ d : ℕ, ∃ f : ℕ → ℕ, ∀ N : ℕ, ∀ (S : Finset (Fin d → ℕ)),
      S ⊆ boxPower d N →
      IsSumFree S.toSet →
      S.card ≤ f N := by
  sorry

end Green6
