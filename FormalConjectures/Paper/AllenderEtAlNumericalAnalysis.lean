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
# Arithmetic identity testing and exact numerical comparison

Allender, Bürgisser, Kjeldgaard-Pedersen, and Miltersen,
*On the Complexity of Numerical Analysis*, SIAM J. Comput. 38(5), 1987–2006 (2009),
https://doi.org/10.1137/070697926.
Author version: https://people.cs.rutgers.edu/~allender/papers/slp.pdf,
§1.4 (root sums, p. 5) and §2 (ACIT and PosSLP, pp. 5–6).

These are questions about deterministic polynomial bit-time on explicit binary
inputs, using the existing TM2 model. Circuit values and root sums are exact.
Neither a unit-cost real machine nor floating-point approximation is substituted.
The definitions reject malformed circuits and allow only the constants 0 and 1.
No degree bound is imposed on ACIT; PosSLP has no variables.

The root-sum question uses nonnegative integer radicands, so all square roots
are real, and keeps the source's signed integer threshold and non-strict ≥ comparison.
-/

namespace AllenderEtAlNumericalAnalysis

open ComplexityTheory AlgebraicProblems

/-- Does integer arithmetic circuit identity testing admit a deterministic polynomial-time
algorithm (§2, ACIT)? -/
@[category research open, AMS 13 68]
theorem arithmeticIdentity_polytime :
    answer(sorry) ↔ HasPolyTimeDecider IsArithmeticIdentity := by
  sorry

/-- Does PosSLP admit a deterministic polynomial-time algorithm (§2)?
The question is whether the integer represented by a closed SLP is strictly positive. -/
@[category research open, AMS 11 68]
theorem positiveSLP_polytime :
    answer(sorry) ↔ HasPolyTimeDecider IsPositiveSLP := by
  sorry

/-- Can one decide $\sum_i \sqrt{d_i} \ge k$ in deterministic polynomial time,
for nonnegative integers $d_i$ and an integer $k$ (§1.4)? -/
@[category research open, AMS 11 68]
theorem sumSquareRoots_polytime :
    answer(sorry) ↔ HasPolyTimeDecider SumSquareRootsAtLeast := by
  sorry

end AllenderEtAlNumericalAnalysis
