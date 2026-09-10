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

Stephen A. Cook and Robert A. Reckhow,
*The Relative Efficiency of Propositional Proof Systems*,
Journal of Symbolic Logic 44(1) (1979), pp.36–50.
https://www.karlin.mff.cuni.cz/~krajicek/cr79.pdf

The conjecture in §1, p.38, predicts that conventional propositional systems
are not polynomially bounded. These are its Frege and Extended Frege instances,
using the six schemes on pp.39–40 and the extension rule in Definition 4.1.

Proof size is total encoded bit length, including repeated subformulas and
binary variable names, not the number of inference steps.
-/

namespace CookReckhow1979

open PropositionalProof

/-- Frege is not polynomially bounded: no one polynomial in formula size bounds
the size of a shortest Frege proof for every tautology. -/
@[category research open, AMS 3 68]
theorem frege_not_polynomially_bounded :
    ¬ PolynomiallyBounded fregeProof := by
  sorry

/-- Extended Frege is not polynomially bounded, even with fresh extension variables.
See also Krajíček, arXiv:1909.03691, §2, p.7. -/
@[category research open, AMS 3 68]
theorem extended_frege_not_polynomially_bounded :
    ¬ PolynomiallyBounded extendedFregeProof := by
  sorry

end CookReckhow1979
