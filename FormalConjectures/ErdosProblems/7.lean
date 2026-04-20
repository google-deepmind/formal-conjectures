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
# Erdős Problem 7

*Reference:* [erdosproblems.com/7](https://www.erdosproblems.com/7)
-/

namespace Erdos7

open Set

/--
Is there a covering system all of whose moduli are odd (and greater than 1)?
-/
@[category research open, AMS 11]
theorem erdos_7 : answer(sorry) ↔
    ∃ (C : StrictCoveringSystem ℤ), ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  sorry

end Erdos7
