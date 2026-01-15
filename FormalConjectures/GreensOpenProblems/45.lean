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
import FormalConjectures.Util.Answer
import FormalConjectures.Util.Category
import FormalConjectures.Util.AMS

/-!
# Ben Green's Open Problem 45

For each prime \(p \le N\), choose a residue class \(a_p \pmod p\).
Is it possible to do this so that every integer \(n \le N\)
lies in at least 10 of the chosen residue classes?
-/

@[category research open]
@[AMS 11] -- Number Theory
theorem GreensOpenProblem45 :
    answer(sorry) := by
  sorry
