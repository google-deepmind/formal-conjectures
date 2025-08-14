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

*Reference:* [erdosproblems.com/591](https://www.erdosproblems.com/591)
-/

open Cardinal Ordinal

universe u

/--
Let $α$ be the infinite ordinal $\omega^{\omega^2}$. Is it true that any red/blue colouring of the
edges of $K_α$ there is either a red $K_α$ or a blue $K_3$.
-/
@[category research open, AMS 3]
theorem erdos_591 : OmegaPowerRamsey (ω^2) 3 ↔ answer(sorry) := by
  sorry
