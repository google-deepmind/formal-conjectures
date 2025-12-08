/-
Copyright 2025 The Formal Conjectures Authors.

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

open Algebra.Group.GrowthRate

/-!
# Gap conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Gromov%27s_theorem_on_groups_of_polynomial_growth#The_gap_conjecture)
-/

namespace GapConjecture

def SuperPolynomial (F : GrowthClass) : Prop :=
  ∀ n : ℕ, ⟦fun m => ↑(m ^ n)⟧ ≤ F

noncomputable
def expSqrt : GrowthClass :=
  ⟦fun n => Real.exp (Real.sqrt n)⟧

/-!
If the growth rate of a finitely generated group $G$ is superpolynomial, then the growth rate is at
least $e^{\sqrt{n}}$.
-/
@[category research open, AMS 20]
theorem gap_conjecture :
  ∀ (G : Type) [Group G] [Group.FG G],
    SuperPolynomial (growthRate G) → growthRate G ≥ expSqrt := by
      sorry

end GapConjecture
