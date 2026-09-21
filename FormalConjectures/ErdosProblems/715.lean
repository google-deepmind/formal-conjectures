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
public import FormalConjectures.ErdosProblems.«182»

/-!
# Erdős Problem 715

*References:*
- [erdosproblems.com/715](https://www.erdosproblems.com/715)
- [Er75] Erdős, P., _Some recent progress on extremal problems in graph theory_. Congr. Numer.
  (1975), 3-14.
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25-42.
- [AFK84] Alon, N. and Friedland, S. and Kalai, G., _Every 4-regular graph plus an edge contains
  a 3-regular subgraph_. J. Combin. Theory Ser. B (1984), 92-93.
- [Ta82] Tashkinov, _Regular subgraphs of regular graphs_. Soviet Math. Dokl. (1982), 37-38.
-/

@[expose] public section

open Erdos182

namespace Erdos715

/--
Does every regular graph of degree $4$ contain a regular subgraph of degree $3$?

A problem of Berge (or Berge and Sauer). The answer is yes, proved by Tashkinov [Ta82].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos715.lean#L35278"]
theorem erdos_715.parts.i : answer(True) ↔
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree 4 → ContainsRegularSubgraph G 3 := by
  sorry

/--
Is there any $r$ such that every regular graph of degree $r$ must contain a regular subgraph of
degree $3$?

The answer is yes: $r=4$ works by Tashkinov [Ta82], and Alon, Friedland, and Kalai [AFK84]
proved that every $r$-regular graph with $r\geq 5$ contains a $3$-regular subgraph.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos715.lean#L35295"]
theorem erdos_715.parts.ii : answer(True) ↔
    ∃ r : ℕ, ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree r → ContainsRegularSubgraph G 3 := by
  sorry

/-- Alon, Friedland, and Kalai [AFK84] proved that every $4$-regular graph plus an edge contains
a $3$-regular subgraph, and hence in particular every $r$-regular graph with $r\geq 5$ contains a
$3$-regular subgraph. -/
@[category research solved, AMS 5]
theorem erdos_715.variants.alon_friedland_kalai (r : ℕ) (hr : 5 ≤ r)
    (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree r) : ContainsRegularSubgraph G 3 := by
  sorry

end Erdos715
