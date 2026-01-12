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
# Erdős Problem 109

*References:*
- [erdosproblems.com/109](https://www.erdosproblems.com/109)
- [MRR19] J. Moreira, F.K. Richter, and D. Robertson, A proof of a sumset conjecture of Erdős,
  Annals of Math. 189 (2019), 605-652.
-/

open Pointwise

namespace Erdos109

/--
Any $A\subseteq \mathbb{N}$ of positive upper density contains a sumset $B+C$ where both $B$ and $C$
are infinite.

The Erdős sumset conjecture. Proved by Moreira, Richter, and Robertson [MRR19].
-/
@[category research solved, AMS 11]
theorem erdos_109 (A : Set ℕ) (h : A.upperDensity > 0) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A := by
  sorry

end Erdos109
