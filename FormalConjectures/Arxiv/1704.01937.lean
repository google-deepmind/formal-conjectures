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
# Promise graph homomorphism hardness

*References:*
* Brakensiek and Guruswami, *Promise Constraint Satisfaction: Algebraic Structure
  and a Symmetric Boolean Dichotomy*, arXiv:1704.01937v2, §1,
  Conjecture 1.2, pp. 3–4, https://arxiv.org/abs/1704.01937v2.
-/

namespace Arxiv.«1704.01937»

open ComplexityTheory Computability.MatrixGraph Computability.PromiseGraph

/-- **Promise graph homomorphism** (Conjecture 1.2): for every fixed pair of finite
loopless undirected nonbipartite graphs $G,H$ with $G\to H$, distinguishing $X\to G$
from $X\not\to H$ is NP-hard under deterministic polynomial-time many-one reductions.
The input $X$ is an explicit binary adjacency matrix of a directed graph, possibly
with loops; homomorphisms must preserve every edge. Ragged matrices are outside
the promises. Target graphs and their sizes are fixed before the reduction, not
part of its input. This is decision, not finding a homomorphism. Under $P\ne NP$,
the claimed hardness excludes polynomial-time separation. -/
@[category research open, AMS 5 68]
theorem promise_graph_homomorphism :
    ∀ g h : Code, ValidGraph g → ValidGraph h →
      Nonbipartite g → Nonbipartite h → Hom g h →
        PromiseNPHard (Yes g) (No h) := by sorry

end Arxiv.«1704.01937»
