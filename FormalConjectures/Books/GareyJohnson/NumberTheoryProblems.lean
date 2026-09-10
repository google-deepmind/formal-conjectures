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
# Bounded quadratic congruences and binary quadratic Diophantine equations

*References:*
- Garey and Johnson, *Computers and Intractability* (1979), AN1 (p. 249) and AN8 (p. 250).
  https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf
- Manders and Adleman, *NP-Complete decision problems for binary quadratics*,
  Journal of Computer and System Sciences 16(2) (1978), 168–184.
  https://doi.org/10.1016/0022-0000(78)90044-2
-/

namespace GareyJohnson1979

open ComplexityTheory NumberTheoryProblems

/-- **QUADRATIC CONGRUENCES** (AN1, p. 249). Input: positive binary integers $a,b,c$.
Property: there is a positive integer $x<c$ with $x^2\equiv a\pmod b$.
The strict input bound is essential; this is not unbounded quadratic residuosity.
This problem is NP-complete, so the nonexistence of a deterministic polynomial-time
decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 11 68]
theorem boundedQuadraticCongruence_not_polytime :
    ¬ HasPolyTimeDecider BoundedQuadraticCongruence := by
  sorry

/-- **QUADRATIC DIOPHANTINE EQUATIONS** (AN8, p. 250). Input: positive binary integers
$a,b,c$. Property: positive integers $x,y$ satisfy $a x^2+b y=c$. Neither witness may
be zero. This problem is NP-complete, so the nonexistence of a deterministic polynomial-time
decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 11 68]
theorem binaryQuadraticDiophantine_not_polytime :
    ¬ HasPolyTimeDecider BinaryQuadraticDiophantine := by
  sorry

end GareyJohnson1979
