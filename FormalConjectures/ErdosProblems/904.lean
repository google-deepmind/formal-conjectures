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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 904

*Reference:* [erdosproblems.com/904](https://www.erdosproblems.com/904)
-/

namespace Erdos904

open Finset

variable {V : Type*} [Fintype V]

/-- An abbreviation for the fixed number of vertices $n$ in the graph. -/
abbrev n (V : Type*) [Fintype V] : ℕ := Fintype.card V

/-- The number of edges of the Turán graph $T(n, r)$, i.e. the Turán number. -/
abbrev turanNumber (n r : ℕ) : ℕ := #(SimpleGraph.turanGraph n r).edgeFinset

/--
A conjecture of Bollobás and Nikiforov on cliques and degrees: every graph $G$ with at least
$\mathrm{turanNumber}(n, r)$ edges (the Turán bound forcing a $K_r$, for $1 \le r \le n$) contains
an $r$-clique $s$ whose vertices have large total degree, namely
$2r \cdot e(G) \le n \cdot \sum_{v \in s} \deg(v)$. This is true: such a clique always exists.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos904.lean"]
theorem erdos_904 (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hr : r ∈ Set.Icc 1 (n V)) (hm : turanNumber (n V) r ≤ #G.edgeFinset) :
    ∃ s, G.IsNClique r s ∧ 2 * r * #G.edgeFinset ≤ n V * ∑ v ∈ s, G.degree v := by
  sorry

end Erdos904
