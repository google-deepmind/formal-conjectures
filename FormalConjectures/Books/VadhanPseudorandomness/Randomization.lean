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
# Eliminating randomness from polynomial-time decision algorithms

*References:*
* Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer
  Science 7(1–3), 2012, §2.2, pp. 17–21, Definitions 2.9, 2.13, 2.15,
  Fact 2.16 and Open Problems 2.10, 2.14, 2.17,
  https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf.
-/

namespace VadhanPseudorandomness

/-- **Derandomization of bounded error** (Vadhan, Open Problem 2.14, p. 20):
$BPP=P$. Every decision problem on bit strings with a randomized polynomial-time
algorithm correct with probability at least $2/3$ on each input has a deterministic
polynomial-time algorithm. Randomized algorithms use polynomially many independent
fair bits and a TM2 time bound on every input/coin-string pair. -/
@[category research open, AMS 3 68]
theorem bpp_eq_p : ComplexityTheory.BPP = ComplexityTheory.P := by
  sorry

/-- **Derandomization of one-sided error** (Vadhan, Open Problem 2.10, p. 19):
$P=RP$. Every bit-string decision problem with a randomized polynomial-time
algorithm having no false positives and accepting each yes-instance with probability
at least $1/2$ has a deterministic polynomial-time algorithm. The TM2 bound holds
on every input/coin-string pair, with polynomially many independent fair bits. -/
@[category research open, AMS 3 68]
theorem p_eq_rp : ComplexityTheory.P = ComplexityTheory.RP := by
  sorry

/-- **Derandomization of zero error** (Vadhan, Open Problem 2.17, p. 21):
$P=ZPP$. Here $ZPP$ is defined as $RP\cap coRP$, following Fact 2.16: both a
bit-string language and its complement have one-sided-error polynomial-time
algorithms. The conjecture gives a deterministic polynomial-time decider for every
such language. This uses the intersection characterization of Las Vegas algorithms,
not a separate expected-running-time operational definition. -/
@[category research open, AMS 3 68]
theorem p_eq_zpp : ComplexityTheory.P = ComplexityTheory.ZPP := by
  sorry

end VadhanPseudorandomness
