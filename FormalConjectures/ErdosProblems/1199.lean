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
# Erdős Problem 1199

*References:*
- [erdosproblems.com/1199](https://www.erdosproblems.com/1199)
- [Hi79] Hindman, Neil, Partitions and sums of integers with repetition.
  J. Combin. Theory Ser. A (1979), 19--32.
- [Ow74] J. Owings, E2494. Amer. Math. Monthly (1974), 902. 
-/

open Pointwise

namespace Erdos1199

/--
Is it true that in any 2-colouring of $\mathbb{N}$ there exists an infinite set $A$
such that all elements of $A+A$ are the same colour?

A conjecture of Owings [Ow74].
-/
@[category research open, AMS 5]
theorem erdos_1199 :
    answer(sorry) ↔
    ∀ (color : ℕ → Fin 2), ∃ (A : Set ℕ),
    A.Infinite ∧ ∀ n ∈ (A+A), ∀ m ∈ (A+A), color n = color m := by 
  sorry

/--
Hindman [Hi79] has shown that this is false for 3-colourings.
-/
@[category research solved, AMS 5]
theorem erdos_1199.variants.three :
    ∃ (color : ℕ → Fin 3), ∀ (A : Set ℕ),
    A.Infinite → ∃ n ∈ (A+A), ∃ m ∈ (A+A), color n ≠ color m := by 
  sorry

end Erdos1199
