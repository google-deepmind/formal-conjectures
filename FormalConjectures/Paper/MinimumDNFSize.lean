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

*References:*
* Allender–Hellerstein–McCabe–Pitassi–Saks, *Minimizing Disjunctive Normal Form
  Formulas and AC⁰ Circuits Given a Truth Table*, SIAM J. Comput. 38(1) (2008),
  pp. 63–84, https://doi.org/10.1137/060664537;
  author version, §2, pp. 3–4, and §3, https://cs.rutgers.edu/~allender/papers/mindnf.pdf.
-/

namespace AllenderEtAl2008

/-- **Min-DNF** (Allender et al., §§2–3) has no deterministic polynomial bit-time
decider. Input: binary arity $n$, a full $2^n$-bit truth table and a binary natural
bound $s$. Property: a DNF with at most $s$ terms computes that table. Size counts
terms, not literals; the empty disjunction is false and an empty conjunction is
true, including at $n=0$. Incorrect table lengths are rejected. Time is measured
in the whole input length, not just $n$. This full-table problem is NP-complete,
so the lower bound is classically equivalent to $P\ne NP$. -/
@[category research open, AMS 68]
theorem minimumDNF_not_polytime : ¬ ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.MinimumDNF := by
  sorry

end AllenderEtAl2008
