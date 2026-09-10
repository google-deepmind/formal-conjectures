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
# Small-Set Expansion Conjecture

*References:*
* Raghavendra and Steurer, *Graph Expansion and the Unique Games Conjecture*,
  STOC 2010, Problem 1 and Conjecture 1.3, pp. 2–3,
  https://www.dsteurer.org/paper/expansion.pdf.
-/

namespace RaghavendraSteurer2010

open ComplexityTheory Computability.SmallSetExpansion

/-- **Small-Set Expansion** (Problem 1 and Conjecture 1.3): for every rational
$0<\eta<1/2$, some fixed rational $0<\delta\le1/2$ makes the following distinction
NP-hard under deterministic polynomial-time many-one reductions. Input: an explicit
loopless, simple, unweighted regular graph with $n$ vertices and its positive degree
$d$, all binary encoded. Yes: some set of exactly $\delta n$ vertices has expansion
at most $\eta$. No: all sets of that size have expansion at least $1-\eta$, where
expansion is crossing edges divided by $d|S|$. Inputs with unattainable positive
size $\delta n$ are excluded from both promises. Under $P\ne NP$, this hardness
would exclude polynomial-time separation. -/
@[category research open, AMS 5 68]
theorem small_set_expansion :
    ∀ η : ℚ, 0 < η → η < 1 / 2 →
      ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 / 2 ∧ PromiseNPHard (Yes η δ) (No η δ) := by sorry

end RaghavendraSteurer2010
