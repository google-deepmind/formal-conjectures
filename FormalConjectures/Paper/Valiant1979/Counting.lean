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
import FormalConjecturesUtil

/-!
# Exact counting and polynomial time

Valiant, *The Complexity of Computing the Permanent* (1979), §2 and Theorem1,
pp.189–193, https://doi.org/10.1016/0304-3975(79)90044-6.

Both questions concern deterministic bit-complexity and exact binary outputs,
not approximation or nonuniform arithmetic circuits. The source establishes
classical counting completeness; those reductions are not formalized here.
-/

namespace Valiant1979

/-- Counting all satisfying assignments of a CNF formula is not computable in
deterministic polynomial time. Variables range over the names occurring in the formula. -/
@[category research open, AMS 3 68]
theorem modelCount_not_polytime : ¬ ComplexityTheory.IsPolyTime ExactCounting.modelCount := by
  sorry

/-- Computing the exact permanent of an explicit 0–1 matrix is not possible
in deterministic polynomial time. Nonsquare row lists are assigned zero. -/
@[category research open, AMS 15 68]
theorem permanent_not_polytime : ¬ ComplexityTheory.IsPolyTime ExactCounting.permanent := by
  sorry

end Valiant1979
