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
# The permanent arithmetic-circuit lower-bound conjecture

Shpilka and Yehudayoff, *Arithmetic circuits: A survey of recent results and open
questions*, Foundations and Trends in Theoretical Computer Science 5(3–4), 207–388,
https://www.cs.tau.ac.il/~shpilka/publications/SY10.pdf,
Definition 1.1, Definition 1.2, Valiant's hypothesis I, and Theorem 1.1
(author-version pp. 2–5).

This is the permanent-circuit formulation over ℚ. The source identifies it with
Valiant's hypothesis using completeness of the permanent in characteristic not two.
That completeness theorem and the VP/VNP equivalence are not formalized here.

The circuit basis is +,× with arbitrary rational constants, and size is the number
of edges. This is a nonuniform algebraic model: there is no computability condition
on the circuit family and no bit-length charge for its constants.
-/

namespace ShpilkaYehudayoff

/-- The permanent over ℚ has no polynomial-size family of arithmetic circuits
(Valiant's hypothesis I and Theorem 1.1). -/
@[category research open, AMS 15 68]
theorem permanent_not_polynomial_size :
    ¬ AlgebraicProblems.HasPolynomialSizePermanentCircuits := by
  sorry

end ShpilkaYehudayoff
