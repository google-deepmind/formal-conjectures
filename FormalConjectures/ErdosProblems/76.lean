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
# Erdős Problem 76

*Reference:* [erdosproblems.com/76](https://www.erdosproblems.com/76)

In any 2-colouring of the edges of $K_n$ there must exist at least
$(1 + o(1)) \, n^2/12$ many edge-disjoint monochromatic triangles.

Conjectured by Erdős, Faudree, and Ordman [Er95][Er97d]. Proved by Gruslys and
Letzter [GrLe20].

The bound is tight: partition $V(K_n)$ into two equal halves, colour edges
between parts red and edges within parts blue — any edge-disjoint monochromatic
triangle must either use 3 blue edges (within a part) or 3 red edges (between
parts), and a careful count shows $\approx n^2/12$ is achievable but not more.

See also OEIS sequence A060407.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics '94 (Catania), Congressus Numerantium 107 (1995).

[Er97d] Erdős, P., _Some of my favourite problems in number theory, combinatorics,
and geometry_.

[Va99, 3.54] See erdosproblems.com/76.

[GrLe20] Gruslys, V. and Letzter, S., _Minimising the number of triangles in a
two-colouring of the edges of $K_n$_, J. Combin. Theory Ser. B (2020).
-/

namespace Erdos76

/-- A 2-edge-colouring of $K_n$ assigns a `Bool` to each unordered pair of vertices.
(Values at diagonal elements $s(v, v)$ are irrelevant.) -/
def EdgeTwoColoring (n : ℕ) := Sym2 (Fin n) → Bool

/-- The set of (non-diagonal) edges of a triangle $T \subseteq V(K_n)$:
all unordered pairs $\{x, y\}$ with $x \neq y$ and $x, y \in T$. -/
def triangleEdges {n : ℕ} (T : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  ((T ×ˢ T).image (fun p : Fin n × Fin n => s(p.1, p.2))).filter (fun e => ¬e.IsDiag)

/-- A 3-vertex set $T \subseteq V(K_n)$ is a monochromatic triangle under colouring `col` if
all three edges of $T$ receive the same colour. -/
def IsMonochromaticTriangle {n : ℕ} (col : EdgeTwoColoring n) (T : Finset (Fin n)) : Prop :=
  T.card = 3 ∧ ∃ c : Bool, ∀ e ∈ triangleEdges T, col e = c

/-- A family $\mathcal{T}$ of triangles is edge-disjoint if any two distinct triangles in
$\mathcal{T}$ share no edge. -/
def IsEdgeDisjointFamily {n : ℕ} (𝒯 : Finset (Finset (Fin n))) : Prop :=
  ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → Disjoint (triangleEdges T₁) (triangleEdges T₂)

/--
**Erdős Problem 76** (Erdős–Faudree–Ordman conjecture, proved by Gruslys–Letzter [GrLe20]):

In any 2-colouring of the edges of $K_n$, there exist at least $(1 + o(1)) \, n^2/12$
edge-disjoint monochromatic triangles.

Formally: for every $\varepsilon > 0$ there exists $N$ such that for all $n \geq N$ and any
2-colouring `col` of the edges of $K_n$, there is an edge-disjoint family of
monochromatic triangles of size at least $(1 - \varepsilon) \cdot n^2 / 12$.
-/
@[category research solved, AMS 5]
theorem erdos_76 : answer(True) ↔
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ col : EdgeTwoColoring n,
    ∃ 𝒯 : Finset (Finset (Fin n)),
      (∀ T ∈ 𝒯, IsMonochromaticTriangle col T) ∧
      IsEdgeDisjointFamily 𝒯 ∧
      (1 - ε) * (n : ℝ) ^ 2 / 12 ≤ (𝒯.card : ℝ) := by
  sorry

/--
**Erdős Problem 76, single-color variant** [Er97d]:

In any 2-colouring of the edges of $K_n$, there exist at least $c \cdot n^2$
edge-disjoint monochromatic triangles *all of the same colour* (choosing the
better colour), for some absolute constant $c > 1/24$.

This is strictly stronger than the main problem: it asks for many edge-disjoint
triangles in a single colour class rather than across both colours.
-/
@[category research open, AMS 5]
theorem erdos_76_single_color : answer(True) ↔
    ∃ c : ℝ, 1 / 24 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ col : EdgeTwoColoring n,
    ∃ (color : Bool) (𝒯 : Finset (Finset (Fin n))),
      (∀ T ∈ 𝒯, IsMonochromaticTriangle col T ∧
        ∀ e ∈ triangleEdges T, col e = color) ∧
      IsEdgeDisjointFamily 𝒯 ∧
      c * (n : ℝ) ^ 2 ≤ (𝒯.card : ℝ) := by
  sorry

end Erdos76
