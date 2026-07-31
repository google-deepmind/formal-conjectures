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
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic

/-!
# Erdős Problem 934

*Reference:* [erdosproblems.com/934](https://www.erdosproblems.com/934)

Let $h_t(d)$ be minimal such that every graph $G$ with $h_t(d)$ edges and maximal
degree $\leq d$ contains two edges whose shortest path between them has length $\ge t$.

Estimate $h_t(d)$.
-/

namespace Erdos934

open SimpleGraph

/--
Distance between two edges in a graph: the minimum length (number of edges) of a
path connecting an endpoint of one edge to an endpoint of the other.
-/
noncomputable def edgeDistance {V : Type*} (G : SimpleGraph V) (e f : Sym2 V) : ℕ := sorry

/--
The minimal number of edges such that any graph with maximum degree ≤ d and at least
`h t d` edges contains a pair of edges at distance ≥ t.
-/
noncomputable def h (t d : ℕ) : ℕ := sorry

/--
A trivial upper bound:
\[
h_t(d) \le (t-1)d^2 + 1.
\]
This follows by counting edges within distance < t of a fixed edge.
The exact value remains open for most parameters.
-/
@[category research, AMS 52]
theorem erdos_934 (t d : ℕ) (ht : t ≥ 2) : h t d ≤ (t - 1) * d^2 + 1 := by
  sorry

-- TODO(firsching): formalize better bounds and possible exact results

end Erdos934
