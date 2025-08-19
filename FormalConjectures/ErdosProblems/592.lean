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
# Erdős Problem 592

*Reference:* [erdosproblems.com/592](https://www.erdosproblems.com/592)
-/

open Cardinal Ordinal

universe u

/--
Determine which countable ordinals $β$ have the property that, if $α = \omega^β$, then in any
red/blue colouring of the edges of $K_α$ there is either a red $K_α$ or a blue $K_3$.
-/
@[category research open, AMS 3]
theorem erdos_592 (β : Ordinal.{u}) : (β.card ≤ ℵ₀) →
  OmegaPowerRamsey β 3 ↔ (answer(sorry) : Ordinal.{u} → Prop) β := by
  sorry

-- TODO(firsching): add condition by Galvin and Larson.
