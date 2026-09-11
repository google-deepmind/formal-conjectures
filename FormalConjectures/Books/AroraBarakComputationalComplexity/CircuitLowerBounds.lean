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
# Uniform classes versus polynomial-size circuits

*References:*
* Arora–Barak, *Computational Complexity: A Modern Approach*, author draft
  dated 2007-01-08, §§6.2–6.3, pp. 106–107, and §13.4.1, p. 245,
  https://theory.cs.princeton.edu/complexity/book.pdf.
* Ryan Williams, *Algorithms for Circuits and Circuits for Algorithms*, CCC 2014,
  §I, §III, Definitions 3.1–3.2 and §III.B,
  https://people.csail.mit.edu/rrw/ccc14-survey.pdf.
-/

namespace AroraBarak

open ComplexityTheory

/-- **NP circuit lower bound** (Arora–Barak, §6.3): some bit-string language in $NP$
has no polynomial-size Boolean circuit family. For every proposed global exponent
$k\ge1$, one input length defeats all circuits with at most $n^k+k$ AND/OR gates.
NOT gates and hardwired constants are free; arbitrary sharing is allowed. A circuit
must be correct on every input of its length, including length zero; the family
need not be computable. Since $P\subseteq P/poly$, this conjecture implies $P\ne NP$. -/
@[category research open, AMS 68]
theorem NP_not_subset_Ppoly : ¬ NP ⊆ Ppoly := by sorry

/-- **EXP circuit lower bound** (Arora–Barak, §6.2; Williams, §I): some bit-string language
decidable in deterministic time $2^{poly(n)}$ has no polynomial-size nonuniform
Boolean circuit family. For every global $k\ge1$, some length $n$ has no circuit
of at most $n^k+k$ AND/OR gates correct on all its inputs. NOT and constants are
free, including at $n=0$; there is no depth, fan-out or family-computability bound.
This compares exponential uniform time with polynomial nonuniform circuit size. -/
@[category research open, AMS 68]
theorem EXP_not_subset_Ppoly : ¬ EXP ⊆ Ppoly := by sorry

/-- **NEXP circuit lower bound** (Arora–Barak, §13.4.1): some bit-string language in
nondeterministic exponential time has no polynomial-size nonuniform Boolean circuit
family. Membership uses one TM2 verifier, certificates of length at most
$2^{p(n)}$, and time at most $2^{q(n)}$ on every eligible certificate, measured in
the original input length $n$. The polynomials are fixed before the inputs.
Circuit size counts AND/OR gates; NOT and hardwired constants are free. No global
$k\ge1$ bounds correct circuits at every length by $n^k+k$, even with uncomputable
choice of a circuit per length. This is a nonuniform circuit lower bound. -/
@[category research open, AMS 68]
theorem NEXP_not_subset_Ppoly : ¬ NEXP ⊆ Ppoly := by sorry

end AroraBarak
