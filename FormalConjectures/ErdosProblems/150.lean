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
# Erdős Problem 150

*Reference:* [erdosproblems.com/150](https://www.erdosproblems.com/150)

A minimal cut of a graph is a minimal set of vertices whose removal disconnects
the graph. Let $c(n)$ be the maximum number of minimal cuts a graph on $n$ vertices
can have. Does $c(n)^{1/n} \to \alpha$ for some $\alpha < 2$?

Asked by Erdős and Nešetřil. Seymour observed that $c(3m+2) \geq 3^m$ via $m$
independent paths of length $4$ joining two vertices.

Proved by Bradač [Br24]: the limit $\alpha = \lim c(n)^{1/n}$ exists and
$\alpha \leq 2^{H(1/3)} = 1.8899\ldots < 2$, where $H(\cdot)$ is the binary entropy
function. This confirms the conjecture. Bradač conjectures the true value is
$\alpha = 3^{1/3}$.

[Er88] Erdős, P., _Problems and results in combinatorics and graph theory_.

[Br24] Bradač, D., _The number of minimal vertex separators_.
-/

open SimpleGraph Real Filter

namespace Erdos150

/-- A set $S$ of vertices is a vertex separator of $G$ if the subgraph induced by
the complement $V \setminus S$ is not connected. -/
def IsVertexSeparator {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ¬(G.induce ((S : Set (Fin n))ᶜ)).Connected

/-- $S$ is a minimal vertex cut of $G$ if $S$ is a vertex separator and no proper
subset of $S$ is also a vertex separator. -/
def IsMinimalVertexCut {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  IsVertexSeparator G S ∧
  ∀ T : Finset (Fin n), T ⊂ S → ¬IsVertexSeparator G T

/-- The number of minimal vertex cuts of $G$. -/
noncomputable def numMinimalVertexCuts {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard { S : Finset (Fin n) | IsMinimalVertexCut G S }

/-- $c(n)$ is the maximum number of minimal vertex cuts over all connected simple
graphs on $n$ vertices. -/
noncomputable def c (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ G : SimpleGraph (Fin n), G.Connected ∧
    numMinimalVertexCuts G = k }

/--
Erdős Problem 150 [Er88] (asked by Erdős and Nešetřil):
Let $c(n)$ be the maximum number of minimal vertex cuts in a graph on $n$ vertices.
Does $c(n)^{1/n} \to \alpha$ for some $\alpha < 2$?

Proved by Bradač [Br24]: the limit $\alpha = \lim c(n)^{1/n}$ exists and
$\alpha \leq 2^{H(1/3)} = 1.8899\ldots < 2$, where $H(\cdot)$ is the binary entropy
function. Seymour's construction gives $c(3m+2) \geq 3^m$, so
$\alpha \geq 3^{1/3} \approx 1.442$. Bradač conjectures that the true value is
$\alpha = 3^{1/3}$.
-/
@[category research solved, AMS 5]
theorem erdos_150 : answer(True) ↔
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
        atTop (nhds α) := by
  sorry

end Erdos150
