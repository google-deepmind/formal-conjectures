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
# Minimum circuit size

*References:*
* Kabanets–Cai, *Circuit Minimization Problem*, STOC 2000, pp. 73–79;
  ECCC version, p. 1, https://eccc.weizmann.ac.il/report/1999/045/.
* Ilango, *SAT Reduces to the Minimum Circuit Size Problem with a Random Oracle*,
  §2.2, p. 16, https://eccc.weizmann.ac.il/report/2023/165/.
-/

namespace KabanetsCai2000

/-- **Minimum circuit size** (Kabanets–Cai, p. 1; Ilango, §2.2) has no deterministic
polynomial bit-time decider. Input: binary arity $n$, the full $2^n$-bit truth table,
and a binary bound $s$. Property: a De Morgan circuit computes the table using at
most $s$ AND/OR gates, with free NOT gates and unrestricted sharing. There are no
primitive constants or oracle gates, so arity-zero instances are rejected; incorrect
table lengths are also rejected. Time is measured in the entire input length.
The problem is in $NP$, so this lower bound implies $P\ne NP$; the cited sources
do not establish deterministic NP-hardness. -/
@[category research open, AMS 68]
theorem minimumCircuit_not_polytime : ¬
    ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.MinimumCircuit := by
  sorry

end KabanetsCai2000
