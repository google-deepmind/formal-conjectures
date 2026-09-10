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

*References:*
* Allender, Bürgisser, Kjeldgaard-Pedersen, and Miltersen,
*On the Complexity of Numerical Analysis*, SIAM J. Comput. 38(5), 1987–2006 (2009),
https://doi.org/10.1137/070697926.
Author version: https://people.cs.rutgers.edu/~allender/papers/slp.pdf,
§1.4 (root sums, p. 5) and §2 (ACIT and PosSLP, pp. 5–6).

-/

namespace AllenderEtAlNumericalAnalysis

open ComplexityTheory AlgebraicProblems

/-- **Arithmetic circuit identity testing** (Allender et al., §2, pp. 5–6) has a
deterministic polynomial bit-time decider. Input: an explicit division-free DAG over
$0,1,+,-,\times$, with binary variable names and prior-gate indices; shared fan-out is
allowed. Property: the output is the zero polynomial over $\mathbb{Z}$. Empty or malformed
programs are rejected. Neither degree nor intermediate-value size is bounded.
This is a derandomization conjecture for a problem in $coRP$. -/
@[category research open, AMS 13 68]
theorem arithmeticIdentity_polytime :
    HasPolyTimeDecider IsArithmeticIdentity := by
  sorry

/-- **PosSLP** (Allender et al., §2, pp. 5–6): is there a deterministic polynomial
bit-time decider for strict positivity of the integer output of a division-free
straight-line program over $0,1,+,-,\times$? Input is the explicit DAG with binary
prior-gate indices, not its expanded integer value. Variables, other constants,
empty programs and invalid references are rejected. This is a two-sided complexity
question, not an assertion of NP-completeness. -/
@[category research open, AMS 11 68]
theorem positiveSLP_polytime :
    answer(sorry) ↔ HasPolyTimeDecider IsPositiveSLP := by
  sorry

/-- **Sum of square roots** (Allender et al., §1.4, p. 5): can one decide
$\sum_i \sqrt{d_i} \ge k$ in deterministic polynomial bit-time, given a binary list
of nonnegative integers $d_i$ and a signed integer $k$? The square roots and comparison
are exact; zero radicands, negative thresholds and the empty sum are permitted.
This is a two-sided complexity question underlying exact Euclidean TSP verification;
no gap promise, rounding or unit-cost real arithmetic is used. -/
@[category research open, AMS 11 68]
theorem sumSquareRoots_polytime :
    answer(sorry) ↔ HasPolyTimeDecider SumSquareRootsAtLeast := by
  sorry

end AllenderEtAlNumericalAnalysis
