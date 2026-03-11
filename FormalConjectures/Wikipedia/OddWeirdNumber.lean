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

/-
# Existence of Odd Weird Numbers

*References:*
- [Wikipedia] (https://en.wikipedia.org/wiki/Weird_number)
- [A006037] (https://oeis.org/A006037)
-/

namespace OddWeirdNumber

/-
The Existence of Odd Weird Number Conjecture asks if there exists
an odd number that is weird.
-/
@[category research open, AMS 11]
theorem existence_odd_weird :
    answer(sorry) ↔ ∃ n : ℕ, n.Weird ∧ Odd n := by
  sorry

end OddWeirdNumber
