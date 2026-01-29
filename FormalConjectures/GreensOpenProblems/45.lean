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
import FormalConjectures.ErdosProblems.«689»

/-!
# Ben Green's Open Problem 45

Can we pick residue classes $a_p(mod p)$, one for each prime `p ⩽ N`,
such that every integer `⩽ N` lies in at least 10 of them?

*References:*
- [Ben Green's Open Problem 45](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.45)
- [erdosproblems.com/689](https://www.erdosproblems.com/689)
-/

namespace Green45

@[category research open, AMS 11]
theorem green_45 : type_of% Erdos689.erdos_689 := by
  sorry

end Green45
