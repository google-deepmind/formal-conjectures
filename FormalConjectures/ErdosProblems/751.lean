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
# Erdős Problem 751

*References:*
- [erdosproblems.com/751](https://www.erdosproblems.com/751)
- [Er94b] Erdős, Paul, Some problems in number theory, combinatorics and combinatorial geometry.
  Math. Pannon. (1994), 261--269.
- [BoVi98] Bondy, J. A. and Vince, A., Cycles in a graph whose lengths differ by one or two.
  J. Graph Theory (1998), 11--15.
-/

namespace Erdos751

/--
Let $G$ be a graph with chromatic number $\chi(G)=4$. If $m_1<m_2<\cdots$ are the lengths of the
cycles in $G$ then can $\min(m_{i+1}-m_i)$ be arbitrarily large?

The answer is no: Bondy and Vince [BoVi98] proved that every graph with minimum degree at least $3$
has two cycles whose lengths differ by at most $2$, and hence the same is true for every graph with
chromatic number $4$.

`erdos_751.variants.finite` below carries the Lean proof. It assumes a finite vertex type,
where this quantifies over any `V : Type`, and the two are joined by de Bruijn-Erdős: a graph
that is not $3$-colourable has a finite subgraph that is not $3$-colourable, and cycles of that
subgraph are cycles of the whole. Mathlib does not have de Bruijn-Erdős, so that step is not
formalised here.
-/
@[category research solved, AMS 5]
theorem erdos_751.parts.i :
    answer(False) ↔
      ∀ k : ℕ, ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = 4 ∧
        ∀ m ∈ G.cycleLengths, ∀ m' ∈ G.cycleLengths, m < m' → m + k ≤ m' := by
  sorry

/--
Let $G$ be a graph with chromatic number $\chi(G)=4$. If $m_1<m_2<\cdots$ are the lengths of the
cycles in $G$ then can $\min(m_{i+1}-m_i)$ be arbitrarily large? Can this happen if the girth of
$G$ is large?

The answer is no: Bondy and Vince [BoVi98] proved that every graph with minimum degree at least $3$
has two cycles whose lengths differ by at most $2$, and hence the same is true for every graph with
chromatic number $4$.
-/
@[category research solved, AMS 5]
theorem erdos_751.parts.ii :
    answer(False) ↔
      ∀ k g : ℕ, ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = 4 ∧ g ≤ G.girth ∧
        ∀ m ∈ G.cycleLengths, ∀ m' ∈ G.cycleLengths, m < m' → m + k ≤ m' := by
  sorry

/--
Bondy and Vince [BoVi98] proved that every graph with minimum degree at least $3$ has two cycles
whose lengths differ by at most $2$.
-/
@[category research solved, AMS 5]
theorem erdos_751.variants.bondy_vince {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : 3 ≤ G.minDegree) :
    ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2 := by
  sorry

/--
The finite case of `erdos_751.parts.i`, which is what the Lean proof establishes: a finite graph
with chromatic number at least $4$ has two cycles whose lengths differ by $1$ or $2$.

The proof reaches this through a $4$-critical subgraph, which supplies the $2$-connectivity and
the vertex count its Bondy-Vince step needs on top of minimum degree $3$. Those extra hypotheses
are why it does not also settle `erdos_751.variants.bondy_vince`, which asks for minimum degree
$3$ alone.

This was formalized in Lean by SpringSense Innovation Institute using ChatGPT.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/SpringSense-Innovation-Institute/ai-for-math-lean/blob/ae3ead960a494cf81b28541c477e50997cb03999/erdos-problems/erdos751/Erdos751/Main.lean#L40-L69"]
theorem erdos_751.variants.finite {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber) :
    ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2 := by
  sorry

end Erdos751
