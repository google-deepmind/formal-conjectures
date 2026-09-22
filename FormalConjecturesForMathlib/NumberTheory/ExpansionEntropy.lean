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
module

public import FormalConjecturesForMathlib.Dynamics.SymbolicDynamics.BlockComplexity
public import FormalConjecturesForMathlib.NumberTheory.NormalNumber
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic

/-!
# Entropy of the expansions of a real number

The entropy of the continued fraction expansion of a real number $\xi$ and of its expansion in
an integer base $b$. Both are the entropy `SymbolicDynamics.blockEntropy` of the sequence of
digits.

*References:*
- [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
  Vol. 193. Cambridge University Press, 2012. Chapter 10.

## Main definitions

* `Real.partQuot`: the sequence of partial quotients of a real number.
* `Real.cfEntropy`: the entropy of the continued fraction expansion of a real number.
* `Real.baseEntropy`: the entropy of the base `b` expansion of a real number.
-/

@[expose] public section

open SymbolicDynamics

namespace Real

/--
The sequence $(c_n)_{n \ge 1}$ of partial quotients of the continued fraction expansion
$\xi = [c_0; c_1, c_2, \ldots]$, indexed from $0$. The integer part $c_0$ is not part of the
sequence. The expansion of an irrational number never terminates, so the default value `0` is
never used for such $\xi$.
-/
noncomputable def partQuot (ξ : ℝ) (n : ℕ) : ℝ :=
  ((GenContFract.of ξ).partDens.get? n).getD 0

/-- The entropy $E(\xi)$ of the continued fraction expansion of $\xi$. -/
noncomputable def cfEntropy (ξ : ℝ) : EReal := blockEntropy (partQuot ξ)

/-- The entropy $E(\xi, b)$ of the base $b$ expansion of $\xi$. -/
noncomputable def baseEntropy (b : ℕ) (ξ : ℝ) : EReal :=
  blockEntropy (NormalNumber.digitSeq b ξ)

end Real
