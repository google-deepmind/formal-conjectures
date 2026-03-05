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
# Erdős Problem 1009

*Reference:* [erdosproblems.com/1009](https://www.erdosproblems.com/1009)

Is it true that, for every $c > 0$, there exists $f(c)$ such that every graph on $n$
vertices with at least $\lfloor n^2/4 \rfloor + k$ edges, where $k < cn$, contains at least
$k - f(c)$ many edge-disjoint triangles?

Erdős proved this for $c < 1/2$. Sauer showed $f(2) \geq 1$. This was proved in
general by Györi [Gy88] who showed $f(c) \ll c^2$, and also that $f(c) = 0$ if
$c < 2$ for odd $n$ or $c < 3/2$ for even $n$.

[Er71] Erdős, P., _Some problems in graph theory_, 1971.

[Gy88] Győri, E., _On the number of edge-disjoint triangles in graphs of given size_,
Combinatorica, 1988.
-/

open SimpleGraph Classical

namespace Erdos1009

/-- A collection of $t$ edge-disjoint triangles in a simple graph on $n$ vertices.
Each triangle is an injective map from three indices to vertices whose image is a clique,
and distinct triangles share no edge (unordered pair of vertices). -/
def HasEdgeDisjointTriangles {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  ∃ (tri : Fin t → Fin 3 → Fin n),
    (∀ i, Function.Injective (tri i)) ∧
    (∀ i (j k : Fin 3), j ≠ k → G.Adj (tri i j) (tri i k)) ∧
    (∀ i₁ i₂, i₁ ≠ i₂ →
      ∀ (j₁ k₁ : Fin 3), j₁ ≠ k₁ →
      ∀ (j₂ k₂ : Fin 3), j₂ ≠ k₂ →
        ¬((tri i₁ j₁ = tri i₂ j₂ ∧ tri i₁ k₁ = tri i₂ k₂) ∨
          (tri i₁ j₁ = tri i₂ k₂ ∧ tri i₁ k₁ = tri i₂ j₂)))

/--
Erdős Problem 1009 [Er71, p.98]:

For every $c > 0$, there exists $f(c)$ such that every graph on $n$ vertices with at
least $\lfloor n^2/4 \rfloor + k$ edges, where $k < cn$, contains at least $k - f(c)$
many edge-disjoint triangles. Proved by Györi [Gy88].
-/
@[category research solved, AMS 5]
theorem erdos_1009 : answer(True) ↔
    ∀ c : ℝ, c > 0 →
    ∃ f : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∀ k : ℕ, (k : ℝ) < c * (n : ℝ) →
    G.edgeFinset.card ≥ n ^ 2 / 4 + k →
    HasEdgeDisjointTriangles G (k - f) := by sorry

end Erdos1009
