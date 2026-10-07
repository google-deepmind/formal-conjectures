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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 803

*References:*
- [erdosproblems.com/803](https://www.erdosproblems.com/803)
- [ErSi70] Erdős, P. and Simonovits, M., _Some extremal problems in graph theory_. Combinatorial
  theory and its applications, I-III (Proc. Colloq., Balatonfüred, 1969) (1970), 377-390.
- [Al08] Alon, Noga, _Problems and results in extremal combinatorics. II_. Discrete Math. (2008),
  4460-4472.
- [JaSu23] Janzer, Oliver and Sudakov, Benny, _Resolution of the Erdős-Sauer problem on regular
  subgraphs_. Forum Math. Pi (2023), Paper No. e19, 13.
-/

@[expose] public section

open Filter Real SimpleGraph

namespace Erdos803

open scoped Classical in
/--
We call a graph $H$ $D$-balanced (or $D$-almost-regular) if the maximum degree of $H$ is at most
$D$ times the minimum degree of $H$.

Is it true that for every $m\geq 1$, if $n$ is sufficiently large, any graph on $n$ vertices with
$\geq n\log n$ edges contains a $O(1)$-balanced subgraph with $m$ vertices and $\gg m\log m$ edges
(where the implied constants are absolute)?

A problem of Erdős and Simonovits [ErSi70]. Alon [Al08] proved this is false: for every $D>1$
and large $n$ there is a graph $G$ with $n$ vertices and $\geq n\log n$ edges such that if $H$ is
a $D$-balanced subgraph then $H$ has $\ll m\sqrt{\log m}+\log D$ many edges.

See also [1077](https://www.erdosproblems.com/1077).
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos803.lean#L448"]
theorem erdos_803 : answer(False) ↔
    ∃ (D c : ℝ), 0 < c ∧ ∀ m ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) * log n ≤ G.edgeSet.ncard →
        ∃ H : G.Subgraph, H.verts.ncard = m ∧ IsBalanced H.coe D ∧
          c * m * log m ≤ H.edgeSet.ncard := by
  sorry

open scoped Classical in
/-- Alon [Al08] proved that for every $D>1$ and large $n$ there is a graph $G$ with $n$ vertices
and $\geq n\log n$ edges such that if $H$ is a $D$-balanced subgraph on $m$ vertices then $H$ has
$\ll m\sqrt{\log m}+\log D$ many edges. -/
@[category research solved, AMS 5]
theorem erdos_803.variants.alon :
    ∃ C : ℝ, ∀ D : ℝ, 1 < D → ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      (n : ℝ) * log n ≤ G.edgeSet.ncard ∧
      ∀ H : G.Subgraph, IsBalanced H.coe D →
        (H.edgeSet.ncard : ℝ) ≤ C * (H.verts.ncard * √(log H.verts.ncard) + log D) := by
  sorry

open scoped Classical in
/-- Janzer and Sudakov [JaSu23] have proved that, for any $k$, if $n$ is sufficiently large then
any graph on $n$ vertices with at least $n\log n$ edges contains a $O(1)$-balanced subgraph on
$m\geq k$ vertices with $\gg_k \frac{\sqrt{\log m}}{(\log\log m)^{3/2}}m$ many edges. -/
@[category research solved, AMS 5]
theorem erdos_803.variants.janzer_sudakov :
    ∃ D : ℝ, ∀ k : ℕ, ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) * log n ≤ G.edgeSet.ncard →
        ∃ H : G.Subgraph, k ≤ H.verts.ncard ∧ IsBalanced H.coe D ∧
          c * (√(log H.verts.ncard) / (log (log H.verts.ncard)) ^ (3 / 2 : ℝ)) *
            H.verts.ncard ≤ H.edgeSet.ncard := by
  sorry

end Erdos803
