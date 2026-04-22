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
import FormalConjectures.Wikipedia.HardyLittlewood

/-!
# Erdős Problem 855

*Reference:* [erdosproblems.com/855](https://www.erdosproblems.com/855)

This is an "eventually" formulation of the Second Hardy–Littlewood conjecture.
-/

open Filter
open scoped Nat.Prime

namespace Erdos855

@[category research open, AMS 11]
theorem erdos_855 : answer(sorry) ↔
    ∀ᶠ x in atTop, ∀ᶠ y in atTop, π (x + y) ≤ π x + π y := by
  sorry

end Erdos855
