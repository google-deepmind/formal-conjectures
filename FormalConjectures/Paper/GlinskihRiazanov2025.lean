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
# Partial minimum branching-program size

*References:*
* Glinskih–Riazanov, *Partial Minimum Branching Program Size Problem Is ETH-Hard*,
  ITCS 2025, pp. 54:1–54:22, Theorem 1 and §2, pp. 54:5–54:6,
  https://doi.org/10.4230/LIPIcs.ITCS.2025.54.
-/

namespace GlinskihRiazanov2025

/-- **Partial minimum branching-program size** (Glinskih–Riazanov, §2) has no
deterministic polynomial bit-time decider. Input: binary arity $n$, a full $2^n$-entry
partial truth table and a binary bound $s$. Property: a deterministic Boolean DAG
with one source and two sinks agrees at every defined entry, using at most $s$
nodes including the sinks. Every non-root node has an incoming edge; repeated
queries are allowed, with no ordering, read-once or width restriction. Incorrect
table lengths are rejected, and $n=0$ has no witnesses. Time is measured in the
whole input length. Theorem 1 supplies ETH-conditional hardness, not deterministic
NP-hardness for this explicit-table representation. -/
@[category research open, AMS 68]
theorem partialMinimumBranchingProgram_not_polytime : ¬
    ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.PartialMinimumBranchingProgram := by
  sorry

end GlinskihRiazanov2025
