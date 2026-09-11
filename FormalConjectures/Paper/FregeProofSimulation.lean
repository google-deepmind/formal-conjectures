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
# Frege does not simulate Extended Frege

*References:*
* Buss, *Propositional Proof Complexity: An Introduction*, Computational Logic
  (1999), pp. 127–178, first open problem at the end of §4, author pp. 12–13,
  https://mathweb.ucsd.edu/~sbuss/ResearchWeb/marktoberdorf97/paper.pdf.
-/

namespace Buss1999

open PropositionalProof

/-- **Frege versus Extended Frege** (Buss, §4, open problem (1)): Frege does not
simulate Extended Frege by proof size. There are no global $C,k$ such that every
Extended Frege proof $\pi$ of every formula has a Frege proof of the same formula
with at most $C(|\pi|+1)^k$ bits. Size counts the full encoded chronological proof
list with binary variable names and repeated subformulas. Both use the complete
six-scheme calculus; Extended Frege additionally allows fresh extension definitions.
No computable translator is required by this simulation notion. -/
@[category research open, AMS 3 68]
theorem frege_does_not_simulate_extended_frege :
    ¬ ProofSimulates fregeProof extendedFregeProof := by
  sorry

end Buss1999
