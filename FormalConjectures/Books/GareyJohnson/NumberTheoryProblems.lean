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
# Quadratic number-theoretic lower-bound formulations

Garey and Johnson, *Computers and Intractability* (1979), AN1 (p. 249) and
AN8 (p. 250), classify these positive-integer decision problems as NP-complete:
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf.

Both entries cite Manders and Adleman, *NP-Complete decision problems for binary
quadratics*, Journal of Computer and System Sciences 16(2) (1978), 168–184:
https://doi.org/10.1016/0022-0000(78)90044-2.

The formulations follow the book's positive witnesses and AN1's strict root bound.
All input integers have binary encodings. These are conjectured lower bounds,
not formal proofs of NP-completeness or equivalence to P versus NP.
-/

namespace GareyJohnson1979

open ComplexityTheory NumberTheoryProblems

/-- No deterministic polynomial-time decider for a positive root $x<c$ of
$x^2 \equiv a \pmod b$, given positive binary-encoded $a,b,c$ (AN1). -/
@[category research open, AMS 11 68]
theorem boundedQuadraticCongruence_not_polytime :
    ¬ HasPolyTimeDecider BoundedQuadraticCongruence := by
  sorry

/-- No deterministic polynomial-time decider for positive solutions $x,y$ of
$a x^2 + b y = c$, given positive binary-encoded $a,b,c$ (AN8). -/
@[category research open, AMS 11 68]
theorem binaryQuadraticDiophantine_not_polytime :
    ¬ HasPolyTimeDecider BinaryQuadraticDiophantine := by
  sorry

end GareyJohnson1979
