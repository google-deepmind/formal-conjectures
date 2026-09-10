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
# Does Frege simulate Extended Frege?

Samuel R. Buss, *Propositional Proof Complexity: An Introduction*,
in Computational Logic (1999), pp.127–178.
https://mathweb.ucsd.edu/~sbuss/ResearchWeb/marktoberdorf97/paper.pdf

The first open problem at the end of §4, author PDF pp.12–13, asks whether
Frege systems (p-)simulate Extended Frege. This statement selects simulation
by proof size, without requiring a computable translator.
-/

namespace Buss1999

open PropositionalProof

/-- Is every Extended Frege proof replaceable by a Frege proof of the same
formula with polynomial overhead in total proof size? -/
@[category research open, AMS 3 68]
theorem frege_simulates_extended_frege :
    answer(sorry) ↔ ProofSimulates fregeProof extendedFregeProof := by
  sorry

end Buss1999
