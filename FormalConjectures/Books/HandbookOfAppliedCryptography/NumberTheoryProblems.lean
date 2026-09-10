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
# Classical number-theoretic hardness conjectures

Menezes, van Oorschot, and Vanstone, *Handbook of Applied Cryptography* (1996),
Chapter 3, Definitions 3.28 (RSA, p. 98), 3.31 (quadratic residuosity, p. 99),
and 3.51 (prime-field discrete logarithms, p. 103):
https://cacr.uwaterloo.ca/hac/about/chap3.pdf.

These worst-case conjectures use the existing deterministic classical TM2 model.
The RSA and discrete-logarithm algorithms must return witnesses, not merely decide
whether witnesses exist. Their output existence and uniqueness are proved in the
supporting module. Correctness is required only on the stated promise; the running-time
bound holds on all inputs. No average-case security assertion, randomized hardness,
NP-completeness claim, or reduction to factoring is included.

The classical qualification matters: Shor's quantum algorithms are outside this model.
https://arxiv.org/abs/quant-ph/9508027v2.
-/

namespace HandbookOfAppliedCryptography

open ComplexityTheory NumberTheoryProblems

/-- No deterministic polynomial-time decider for quadratic residuosity when the modulus
is odd and composite and the input residue has Jacobi symbol one (Definition 3.31). -/
@[category research open, AMS 11 68]
theorem quadraticResiduosity_not_polytime :
    ¬ HasPolyTimePromiseDecider ResiduosityPromise IsQuadraticResidue := by
  sorry

/-- No deterministic polynomial-time solver returning a canonical RSA root for every
valid public input $(n,e,c)$, without receiving the factors of $n$ (Definition 3.28). -/
@[category research open, AMS 11 68]
theorem rsaInversion_not_polytime :
    ¬ HasPolyTimeSolver RSAPromise RSAOutput := by
  sorry

/-- No deterministic polynomial-time solver returning $0 \le x \le p-2$ with
$g^x \equiv b \pmod p$ for every prime-field generator $g$ and nonzero target $b$
(Definition 3.51). -/
@[category research open, AMS 11 68]
theorem discreteLogarithm_not_polytime :
    ¬ HasPolyTimeSolver DiscreteLogarithmPromise DiscreteLogarithmOutput := by
  sorry

end HandbookOfAppliedCryptography
