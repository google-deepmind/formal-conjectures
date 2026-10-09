/-
Copyright 2025 The Formal Conjectures Authors.

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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
-/

@[expose] public section

open Filter SimpleGraph

open scoped Topology Real

namespace Erdos74

open Erdos74

universe u

/-!
The function $h_G(n)$ of [EHS82] (the least $k$ such that every subgraph of $G$ on $n$ vertices
can be made bipartite by deleting at most $k$ edges) is
`SimpleGraph.maxSubgraphEdgeDistToBipartite`, defined in `FormalConjecturesForMathlib`.

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/

/--
Let $f(n)\to \infty$ possibly very slowly.
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $f(n)$ edges?

The answer is no. A machine-checked disproof constructs a function $f(n) \to \infty$ for which
every graph satisfying this local deletion bound has finite chromatic number.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/tadamcz/erdos74/blob/e127ee587c7c91267eecdb3569443d2b0ad64b52/Erdos74/Resolutions/Erdos74_118usd_22h.lean#L2511"]
theorem erdos_74 : answer(False) ↔ ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) := by
  sorry

/--
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $\sqrt{n}$ edges?
-/
@[category research open, AMS 5]
theorem erdos_74.variants.sqrt : answer(sorry) ↔
    ∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ (n : ℝ).sqrt := by
  sorry

-- TODO(firsching): add the remaining statements/comments

end Erdos74
