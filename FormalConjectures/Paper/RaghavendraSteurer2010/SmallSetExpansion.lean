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

Reference: Prasad Raghavendra and David Steurer, *Graph Expansion and the
Unique Games Conjecture*, STOC 2010, Problem 1 and Conjecture 1.3, pp.2–3:
https://www.dsteurer.org/paper/expansion.pdf.

We use the paper's regular unweighted convention and sets of exactly delta
times the vertex count. Delta is positive, rational and at most one half;
inputs must admit that exact size. The cofinal range $0<\eta<1/2$ keeps the
two expansion promises disjoint.
-/

namespace RaghavendraSteurer2010

open ComplexityTheory Computability.SmallSetExpansion

/-- For arbitrarily small positive $\eta$, some fixed positive set density
makes it NP-hard to distinguish a set with expansion at most $\eta$ from
expansion at least $1-\eta$ for every set of that exact size. -/
@[category research open, AMS 5 68]
theorem small_set_expansion :
    ∀ η : ℚ, 0 < η → η < 1 / 2 →
      ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 / 2 ∧ PromiseNPHard (Yes η δ) (No η δ) := by sorry

end RaghavendraSteurer2010
