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
# Erdős Problem 832

*Reference:* [erdosproblems.com/832](https://www.erdosproblems.com/832)

Let $r \geq 3$ and $k$ be sufficiently large in terms of $r$. Is it true that every
$r$-uniform hypergraph with chromatic number $k$ has at least $\binom{(r-1)(k-1)+1}{r}$
edges, with equality only for the complete graph on $(r-1)(k-1)+1$ vertices?

When $r = 2$ it is a classical fact that chromatic number $k$ implies at least
$\binom{k}{2}$ edges. Erdős asked for $k$ to be large since he knew the conjecture to
be false for $r = k = 3$ (Steiner triples with 7 vertices and 7 edges).

This was disproved by Alon [Al85] for all $r \geq 4$. The case $r = 3$ remains open.

[Er74d] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and
differences_. Mathematics of Ramsey Theory (1974).

[Al85] Alon, N., _Hypergraphs with high chromatic number_. Graphs and Combinatorics (1985).
-/

namespace Erdos832

/-- An $r$-uniform hypergraph on a finite vertex set $V$: a collection of
$r$-element subsets of $V$. -/
structure UniformHypergraph (V : Type*) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- A proper $k$-coloring of a hypergraph: a vertex coloring such that no edge
is monochromatic (for every edge, not all vertices receive the same color). -/
def UniformHypergraph.IsProperColoring {V : Type*} [DecidableEq V] {r : ℕ}
    (H : UniformHypergraph V r) (k : ℕ) (f : V → Fin k) : Prop :=
  ∀ e ∈ H.edges, ∀ c : Fin k, ∃ v ∈ e, f v ≠ c

/-- The chromatic number of a uniform hypergraph: the minimum number of colors
needed for a proper coloring (no monochromatic edge). -/
noncomputable def UniformHypergraph.chromaticNumber {V : Type*} [DecidableEq V]
    [Fintype V] {r : ℕ} (H : UniformHypergraph V r) : ℕ :=
  sInf {k : ℕ | k ≥ 1 ∧ ∃ f : V → Fin k, H.IsProperColoring k f}

/--
**Erdős Problem 832** [Er74d]:

For $r \geq 3$ and $k$ sufficiently large (in terms of $r$), is it true that every
$r$-uniform hypergraph with chromatic number $k$ has at least
$\binom{(r-1)(k-1)+1}{r}$ edges?

This was disproved by Alon [Al85] for all $r \geq 4$.
-/
@[category research solved, AMS 5]
theorem erdos_832 : answer(False) ↔
    ∀ r : ℕ, r ≥ 3 → ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
    ∀ (V : Type) [DecidableEq V] [Fintype V] (H : UniformHypergraph V r),
      H.chromaticNumber = k →
      H.edges.card ≥ Nat.choose ((r - 1) * (k - 1) + 1) r := by
  sorry

/--
**Erdős Problem 832, $r = 3$ case** [Er74d]:

For $k$ sufficiently large, does every $3$-uniform hypergraph with chromatic number $k$
have at least $\binom{2(k-1)+1}{3}$ edges?

The case $r = 3$ remains open.
-/
@[category research open, AMS 5]
theorem erdos_832.variants.r_eq_3 : answer(sorry) ↔
    ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
    ∀ (V : Type) [DecidableEq V] [Fintype V] (H : UniformHypergraph V 3),
      H.chromaticNumber = k →
      H.edges.card ≥ Nat.choose (2 * (k - 1) + 1) 3 := by
  sorry

end Erdos832
