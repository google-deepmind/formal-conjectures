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
# Symbolic determinant identity testing

Ivanyos, Karpinski, Qiao, and Santha,
*Generalized Wong sequences and their applications to Edmonds' problems*,
https://arxiv.org/abs/1307.6429v2, §1, pp. 1–3.

The input is an explicit square matrix of homogeneous linear forms with integer
coefficients. SDIT asks whether its determinant is a nonzero commutative polynomial,
equivalently whether some specialization is nonsingular. Coefficients and variable
indices are binary encoded. The conjectured algorithm uses polynomial bit-time.

No rank-one, triangularizability, or other tractable matrix-space restriction is
imposed. This is not the noncommutative rank problem.
-/

namespace Arxiv.«1307.6429»

open ComplexityTheory AlgebraicProblems

/-- Is symbolic determinant identity testing over the integers in deterministic
polynomial time (§1)? The accepted instances have a nonzero determinant polynomial. -/
@[category research open, AMS 15 68]
theorem symbolicDeterminant_polytime :
    answer(sorry) ↔ HasPolyTimeDecider SymbolicNonsingular := by
  sorry

end Arxiv.«1307.6429»
