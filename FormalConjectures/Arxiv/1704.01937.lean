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

Reference: Joshua Brakensiek and Venkatesan Guruswami, *Promise Constraint
Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy*,
arXiv:1704.01937v2, §1, Conjecture 1.2, pp.3–4:
https://arxiv.org/abs/1704.01937v2.

The fixed targets are finite, undirected, loopless and non-bipartite, with a
homomorphism from the strict target to the relaxed target. Inputs may be
directed, as in the source's promise digraph homomorphism definition.
This is the decision problem; no output homomorphism is requested.
-/

namespace Arxiv.«1704.01937»

open ComplexityTheory Computability.MatrixGraph Computability.PromiseGraph

/-- For every such pair $G,H$, it is NP-hard to distinguish $X\to G$ from
$X\not\to H$. Neither the target graphs nor their sizes are part of the input. -/
@[category research open, AMS 5 68]
theorem promise_graph_homomorphism :
    ∀ g h : Code, ValidGraph g → ValidGraph h →
      Nonbipartite g → Nonbipartite h → Hom g h →
        PromiseNPHard (Yes g) (No h) := by sorry

end Arxiv.«1704.01937»
