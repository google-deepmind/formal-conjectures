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
# Polynomial-time questions for quadratic residuosity, RSA and discrete logarithms

*References:*
- Menezes, van Oorschot, and Vanstone, *Handbook of Applied Cryptography* (1996),
  Chapter 3, Definitions 3.28 (p. 98), 3.31 (p. 99), and 3.51 (p. 103).
  https://cacr.uwaterloo.ca/hac/about/chap3.pdf
- Shor, *Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms
  on a Quantum Computer*, arXiv:quant-ph/9508027v2.
  https://arxiv.org/abs/quant-ph/9508027v2
-/

namespace HandbookOfAppliedCryptography

open ComplexityTheory NumberTheoryProblems

/-- **QUADRATIC RESIDUOSITY** (Definition 3.31, p. 99). Input: a binary modulus $n$
and signed integer representative $a$, promised that $n$ is odd and composite and
the Jacobi symbol $(a/n)$ is one. Does a deterministic classical polynomial-time algorithm
decide whether $a$ is a square modulo $n$? Correctness is required on the promise;
the time bound applies to every input. This is a two-sided computability question, like
factoring in `PolyTime.isPolyTime_primeFactorsList`. A negative answer would imply
$P\ne NP$; the converse is not known. It is not an average-case security statement. -/
@[category research open, AMS 11 68 94]
theorem quadraticResiduosity_polytime :
    answer(sorry) ↔ HasPolyTimePromiseDecider ResiduosityPromise IsQuadraticResidue := by
  sorry

/-- **RSA INVERSION** (Definition 3.28, p. 98). Input: binary integers $(n,e,c)$,
promised that $n=pq$ for distinct odd primes, $e>0$, and
$\gcd(e,(p-1)(q-1))=1$. The factors are not supplied; $c$ may be any signed representative.
Does a deterministic classical polynomial-time algorithm return $0\le m<n$ with
$m^e\equiv c\pmod n$ on every promised input, with its time bound holding on all inputs?
This is a two-sided search-computability question, not an existence decision or average-case
security claim. A negative answer would imply $P\ne NP$; the converse is not known.
See also the factoring question `PolyTime.isPolyTime_primeFactorsList`. -/
@[category research open, AMS 11 68 94]
theorem rsaInversion_polytime :
    answer(sorry) ↔ HasPolyTimeSolver RSAPromise RSAOutput := by
  sorry

/-- **PRIME-FIELD DISCRETE LOGARITHM** (Definition 3.51, p. 103). Input: binary integers
$(p,g,b)$, promised that $p$ is prime, $0<g,b<p$, and $g$ generates the nonzero residues
modulo $p$. Does a deterministic classical polynomial-time algorithm return
$0\le x<p-1$ with $g^x\equiv b\pmod p$ on every promised input, with its time bound
holding on all inputs? This is a two-sided search-computability question, not an existence
decision or average-case security claim. A negative answer would imply $P\ne NP$;
the converse is not known. See also `PolyTime.isPolyTime_primeFactorsList`; quantum
algorithms use a different computational model. -/
@[category research open, AMS 11 68 94]
theorem discreteLogarithm_polytime :
    answer(sorry) ↔ HasPolyTimeSolver DiscreteLogarithmPromise DiscreteLogarithmOutput := by
  sorry

end HandbookOfAppliedCryptography
