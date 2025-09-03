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

/-!
# Erdős Problem 325
*Reference:* [erdosproblems.com/325](https://www.erdosproblems.com/325)
-/

open Asymptotics Filter

namespace Erdos325

/-- A predicate for $n$ to be the sum of three $k$th powers. -/
def IsSumThreePower (k n : ℕ) : Prop := ∃ a b c, a ^ k + b ^ k + c ^ k = n

/-- The number of integers $\leq x$ which are the sum of three $k$th powers. -/
noncomputable def cardIsSumThreePowerBelow (k x : ℕ) : ℕ :=
  {n ∈ Set.Iic x | IsSumThreePower k n}.ncard

/--
Writing $f_{k, 3}(x)$ for the number of integers $\leq x$ which are the sum of three $k$th powers,
is it true that $f_{k, 3}(x) \gg x ^ (3 / k)$?
-/
@[category research open, AMS 11]
theorem erdos_325 :
    (∀ k : ℕ, 3 ≤ k → (fun x : ℕ => (x : ℝ) ^ (3 / k : ℝ)) =O[atTop]
      (fun x : ℕ => (cardIsSumThreePowerBelow k x : ℝ))) ↔ answer(sorry) := by
  sorry

/--
Writing $f_{k, 3}(x)$ for the number of integers $\leq x$ which are the sum of three $k$th powers,
is it even true that $f_{k, 3}(x) \gg_\epsilon x ^ (3 / k - \epsilon)$?
-/
@[category research open, AMS 11]
theorem erdos_325.variants.weaker :
    (∀ ε > 0, ∀ k : ℕ, 3 ≤ k → (fun x : ℕ => (x : ℝ) ^ ((3 / k : ℝ) - ε)) =O[atTop]
      (fun x => (cardIsSumThreePowerBelow k x : ℝ))) ↔ answer(sorry) := by
  sorry

/--
For $k = 3$, the best known is due to Wooley [Wo15]
[Wo15] Wooley, Trevor D., Sums of three cubes, II. Acta Arith. (2015), 73-100.
-/
@[category research solved, AMS 11]
theorem erdos_325.variants.wooley :
    (fun x : ℕ => (x : ℝ) ^ (0.917 : ℝ)) =O[atTop] (fun x => (cardIsSumThreePowerBelow 3 x : ℝ)) :=
  sorry

end Erdos325
