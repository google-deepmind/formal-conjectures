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
# Erdős Problem 1021

*Reference:* [erdosproblems.com/1021](https://www.erdosproblems.com/1021)

Is it true that, for every $k \ge 3$, there is a constant $c_k > 0$ such that
$$\mathrm{ex}(n, G_k) \ll n^{3/2 - c_k},$$
where $G_k$ is the 1-subdivision of $K_k$: the bipartite graph between
$\{y_1, \ldots, y_k\}$ and $\{z_1, \ldots, z_{\binom{k}{2}}\}$, with each $z_j$ joined to a
unique pair of $y_i$?

A conjecture of Erdős and Simonovits [Er71, p.103][Er74c, p.79]. Erdős [Er64c]
proved $\mathrm{ex}(n, C_6) \ll n^{1+1/3}$; this was also proved by
Bondy–Simonovits [BoSi74]. The general conjecture was proved by Conlon and Lee
[CoLe21] with $c_k = 6^{-k}$, later improved to $c_k = 1/(4k-6)$ by
Janzer [Ja19].

[Er64c] Erdős, P., _On extremal problems of graphs and generalized graphs_.
Israel J. Math. 2 (1964), 183–190.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proceedings of Conference, Oxford, 1969)
(1971), 97–109.

[BoSi74] Bondy, J.A. and Simonovits, M., _Cycles of even length in graphs_.
J. Combin. Theory Ser. B 16 (1974), 97–105.

[CoLe21] Conlon, D. and Lee, J., _On the extremal number of subdivisions_.
Int. Math. Res. Not. IMRN (2021), 9122–9145.

[Ja19] Janzer, O., _Improved bounds for the extremal number of subdivisions_.
Electron. J. Combin. 26 (2019), Paper No. 3.3, 6 pp.
-/

open SimpleGraph Classical

namespace Erdos1021

/-- Adjacency in the 1-subdivision of $K_k$. Vertices are "original" (`Fin k`) or
"edge" (`{(i, j) : i < j}`). Each edge-vertex is adjacent to exactly its two
original endpoints. -/
def subdivKAdj (k : ℕ) :
    Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2} →
    Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2} → Prop
  | .inl a, .inr ⟨⟨i, j⟩, _⟩ => a = i ∨ a = j
  | .inr ⟨⟨i, j⟩, _⟩, .inl a => a = i ∨ a = j
  | _, _ => False

/-- The 1-subdivision of $K_k$. The vertex set is the disjoint union of the
$k$ original vertices and the $\binom{k}{2}$ edge-subdivision vertices.
Each edge-vertex is adjacent to exactly the two endpoints of its
corresponding edge in $K_k$. -/
def subdivisionKComplete (k : ℕ) :
    SimpleGraph (Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2}) where
  Adj := subdivKAdj k
  symm := by
    intro v w h
    rcases v with a | ⟨⟨i, j⟩, hij⟩ <;> rcases w with b | ⟨⟨i', j'⟩, hij'⟩ <;> exact h
  loopless := fun v h => by rcases v with a | ⟨⟨i, j⟩, hij⟩ <;> exact h

/-- A graph $G$ contains $H$ as a subgraph if there is an injective vertex map
that sends edges to edges. -/
def containsSubgraph {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem 1021 [Er71, p.103][Er74c, p.79]:

For every $k \ge 3$, there exists $c_k > 0$ and $C > 0$ such that every $n$-vertex
graph not containing the 1-subdivision of $K_k$ as a subgraph has at most
$C \cdot n^{3/2 - c_k}$ edges.

Proved by Conlon and Lee [CoLe21] with $c_k = 6^{-k}$. Improved to
$c_k = 1/(4k-6)$ by Janzer [Ja19].
-/
@[category research solved, AMS 5]
theorem erdos_1021 : answer(True) ↔
    ∀ (k : ℕ), k ≥ 3 →
    ∃ (c : ℝ), c > 0 ∧ ∃ (C : ℝ), C > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬containsSubgraph G (subdivisionKComplete k) →
    (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2 - c) := by sorry

/--
The special case $k = 3$ of Erdős Problem 1021: the 1-subdivision of $K_3$ is
the 6-cycle $C_6$. Bondy and Simonovits [BoSi74] proved that
$\mathrm{ex}(n, C_6) \le C \cdot n^{1 + 1/3}$, giving $c_3 = 1/6$ (since
$3/2 - 1/6 = 4/3 = 1 + 1/3$). This is much stronger than the general bound
$c_k = 6^{-k}$ of Conlon–Lee.
-/
@[category research solved, AMS 5]
theorem erdos_1021_C6 :
    ∃ (C : ℝ), C > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬containsSubgraph G (subdivisionKComplete 3) →
    (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3) := by sorry

end Erdos1021
