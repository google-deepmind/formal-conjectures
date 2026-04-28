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
# Erdős Problem 591

*References:*
- [erdosproblems.com/591](https://www.erdosproblems.com/591)
- [Sc10] Schipperus, Rene, Countable partition ordinals. Ann. Pure Appl. Logic (2010), 1195-1215.
-/

open Cardinal Ordinal

namespace Erdos591

universe u

/--
Let $α$ be the infinite ordinal $\omega^{\omega^2}$. Is it true that any red/blue colouring of the
edges of $K_α$ there is either a red $K_α$ or a blue $K_3$?

This is true and was proved independently by Schipperus [Sc10] and Darby.
-/
@[category research solved, AMS 3]
theorem erdos_591 : answer(True) ↔ OrdinalCardinalRamsey (ω ^ ω ^ 2) (ω ^ ω ^ 2) 3 := by
  sorry

end Erdos591
