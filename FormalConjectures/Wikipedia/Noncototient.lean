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
# Conjectures about Nonvototient Numbers

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Noncototient)
-/

namespace Noncototient
/--
A number n is a Noncototient if the equation n = k - φ(k) has no solution where φ is Eulers totient
function.
-/
def Noncototient (n : ℕ) : Prop := ¬∃ k : ℕ, n = k - (Nat.totient k)

/--
All Noncototients are even.
-/
@[category research open, AMS 11]
theorem Noncototient_even (n : ℕ) (h : Noncototient n) : Even n := by
  sorry

end Noncototient
