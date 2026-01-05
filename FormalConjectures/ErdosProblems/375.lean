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
# Erdős Problem 375

*References:*
 - [erdosproblems.com/375](https://www.erdosproblems.com/375)
 - [Bi28] Biernacki, Miécislas, Sur les équations algébriques contenant des paramétres arbitraires.
    (1928), 145.
-/

open Set Filter Topology

namespace Erdos375

@[category research open, AMS 30]
theorem erdos_375 : answer(sorry) ↔ ∀ n ≥ 1, ∀ k, (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ (n + i + 1) := by sorry

end Erdos375
