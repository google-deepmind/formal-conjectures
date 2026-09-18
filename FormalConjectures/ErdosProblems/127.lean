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
# Erdős Problem 127

*References:*
- [erdosproblems.com/127](https://www.erdosproblems.com/127)
- [Er97b] Erdős, Paul, *Some old and new problems in various branches of combinatorics*. Discrete
  Math. (1997), 227-231.
- [Ed73] Edwards, C. S., *Some extremal properties of bipartite subgraphs*. Canadian J. Math.
  (1973), 475-485.
- [Al96] Alon, Noga, *Bipartite subgraphs*. Combinatorica (1996), 301-311.
-/

@[expose] public section

open Filter Asymptotics SimpleGraph

namespace Erdos127

/-- `f m` is the largest `k` such that every graph with `m` edges contains a bipartite subgraph
with at least $\frac{m}{2}+\frac{\sqrt{8m+1}-1}{8}+k$ edges. -/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      (m : ℝ) / 2 + (√(8 * m + 1) - 1) / 8 + k ≤ H.edgeSet.ncard}

/--
Let $f(m)$ be maximal such that every graph with $m$ edges must contain a bipartite graph with
$$\geq \frac{m}{2}+\frac{\sqrt{8m+1}-1}{8}+f(m)$$
edges. Is there an infinite sequence of $m_i$ such that $f(m_i)\to \infty$?

Conjectured by Erdős, Kohayakava, and Gyárfás [Er97b]. Edwards [Ed73] proved that $f(m)\geq 0$
always. Note that $f(\binom{n}{2})= 0$, taking $K_n$. Solved by Alon [Al96], who showed
$f(n^2/2)\gg n^{1/2}$, and also showed that $f(m)\ll m^{1/4}$ for all $m$. The best possible
constant in $f(m)\leq Cm^{1/4}$ is unknown.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos127.lean#L585"]
theorem erdos_127 : answer(True) ↔ ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
    Tendsto (fun i => f (m i)) atTop atTop := by
  sorry

/-- Edwards [Ed73] proved that every graph with $m$ edges contains a bipartite subgraph with at
least $\frac{m}{2}+\frac{\sqrt{8m+1}-1}{8}$ edges. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos127.lean#L89"]
theorem erdos_127.variants.edwards {V : Type*} [Finite V] (G : SimpleGraph V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      (G.edgeSet.ncard : ℝ) / 2 + (√(8 * G.edgeSet.ncard + 1) - 1) / 8 ≤ H.edgeSet.ncard := by
  sorry

/-- Alon [Al96] showed that $f(m)\ll m^{1/4}$ for all $m$. -/
@[category research solved, AMS 5]
theorem erdos_127.variants.alon_upper : ∃ C : ℝ, ∀ m : ℕ, (f m : ℝ) ≤ C * (m : ℝ) ^ (1 / 4 : ℝ) := by
  sorry

end Erdos127
