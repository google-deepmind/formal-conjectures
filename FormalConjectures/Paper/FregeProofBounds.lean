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
# Proof-size lower bounds for Frege and Extended Frege

*References:*
* Cook and Reckhow, *The Relative Efficiency of Propositional Proof Systems*,
  JSL 44(1) (1979), pp. 36–50, §1 conjecture p. 38, six schemes pp. 39–40,
  and Definition 4.1, https://www.karlin.mff.cuni.cz/~krajicek/cr79.pdf.
-/

namespace CookReckhow1979

open PropositionalProof

/-- **Frege proof-size lower bound** (Cook–Reckhow, §1): no global constants
$C,k$ bound shortest proofs of all tautologies $A$ by $C(|A|+1)^k$ bits. The calculus
is the complete von Neumann–Church six-scheme system on pp. 39–40 with modus ponens.
Formulas are negation/implication trees with binary variable names; proof size counts
the full encoded list, not steps or shared subexpressions. This lower bound follows
from $NP\ne coNP$, without asserting the converse. -/
@[category research open, AMS 3 68]
theorem frege_not_polynomially_bounded :
    ¬ PolynomiallyBounded fregeProof := by
  sorry

/-- **Extended Frege proof-size lower bound** (Cook–Reckhow, §1 and Definition 4.1):
no global $C,k$ bound shortest proofs of all tautologies $A$ by $C(|A|+1)^k$ bits.
The complete six-scheme Frege calculus is augmented by $q\leftrightarrow D$, where
$q$ is absent from $D$, earlier lines and the final conclusion. Proof size includes
all encoded formulas and repeated subformulas, not just inference steps. This
lower bound follows from $NP\ne coNP$, without asserting the converse. -/
@[category research open, AMS 3 68]
theorem extended_frege_not_polynomially_bounded :
    ¬ PolynomiallyBounded extendedFregeProof := by
  sorry

end CookReckhow1979
