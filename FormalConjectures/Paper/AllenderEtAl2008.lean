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
# Truth-table DNF minimization

Allender–Hellerstein–McCabe–Pitassi–Saks, *Minimizing Disjunctive Normal Form
Formulas and AC⁰ Circuits Given a Truth Table*, SIAM Journal on Computing 38(1)
(2008), pp. 63–84, https://doi.org/10.1137/060664537.
Author version, §2 pp. 3–4 and §3:
https://cs.rutgers.edu/~allender/papers/mindnf.pdf.

This is the full-truth-table decision problem Min-DNF, not the sparse positive
sample representation, partial-table version, or formula-input version.
Size is the number of terms, not literals. The threshold is a binary natural
number. Empty disjunction and empty conjunction represent false and true.
The paper proves NP-completeness; the conjecture below asks for the associated
unconditional deterministic polynomial-time lower bound, not that known theorem.
-/

namespace AllenderEtAl2008

/-- Full-truth-table Min-DNF has no deterministic polynomial-time decider. -/
@[category research open, AMS 3 68]
theorem minimumDNF_not_polytime : ¬ ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.MinimumDNF := by
  sorry

end AllenderEtAl2008
