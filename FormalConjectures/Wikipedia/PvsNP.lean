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
# P vs NP

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/P_versus_NP_problem)
-/

namespace PvsNP

/--
The type of complexity classes over an alphabet `α` is the set of languages over `α`.
-/
def ComplexityClass (α : Type*) := Set (Language α)




/--
The class P is the set of languages over an alphabet `α`
decidable in polynomial time by a deterministic Turing machine
-/
def P {α : Type*} [Nontrivial α] : ComplexityClass α :=
  { L | ∃ M : Turing.TM2ComputableInPolyTime


/--

-/
@[category research open, AMS 68]
theorem PvsNP : sorry := by
  sorry

end PvsNP
