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
# Erdős Problem 1196

*Reference:* [erdosproblems.com/1196](https://www.erdosproblems.com/1196)
-/

namespace Erdos1196

open scoped Asymptotics

-- TODO(Paul-Lez): add this to ForMathlib. I suspect this is the right generalisation from the natural number case?
/-- A set is primitive if no non-associated elements of the set divide each other. -/
def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y

/--
Is it true that, for any $x$, if $A\subset [x,\infty)$ is a primitive set of integers (so that no distinct elements of $A$ divide each other) then$$\sum_{a\in A}\frac{1}{a\log a}&#60; 1+o(1),$$where the $o(1)$ term $\to 0$ as $x\to \infty$?
-/
@[category research solved, AMS 11]
theorem erdos_1196 :
    answer(True) ↔ ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧ ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x, IsPrimitive A →
       ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x  := by
  sorry

end Erdos1196
