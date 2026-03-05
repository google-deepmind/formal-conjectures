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
# Erdős Problem 926

*Reference:* [erdosproblems.com/926](https://www.erdosproblems.com/926)

Is it true that $\mathrm{ex}(n; H_k) \ll_k n^{3/2}$, where $H_k$ is the graph on vertices
$x, y_1, \ldots, y_k, z_1, \ldots, z_{\binom{k}{2}}$ in which $x$ is adjacent to every $y_i$ and
each pair $y_i, y_j$ is adjacent to a unique $z_{ij}$?

[Er69b] Erdős, P., 1969.

[Er71] Erdős, P., 1971.

[Er74c] Erdős, P., 1974.

[Er93] Erdős, P., 1993.

[Fu91] Füredi, Z., 1991.

[AKS03] Alon, N., Krivelevich, M., and Sudakov, B., 2003.
-/

open SimpleGraph

namespace Erdos926

/-- An injective graph homomorphism from $H$ to $G$; witnesses that $G$ contains a
subgraph isomorphic to $H$. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number $\mathrm{ex}(n; H)$: the maximum number of edges in a simple graph on $n$
vertices that contains no copy of $H$ as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬ContainsSubgraph F H ∧ F.edgeFinset.card = m}

/-- Vertex type for the graph $H_k$: one center vertex $x$, $k$ spoke vertices
$y_1, \ldots, y_k$, and one pair vertex $z_{ij}$ for each pair $(i, j)$ with $i < j \leq k$. -/
abbrev HkVertex (k : ℕ) := Unit ⊕ Fin k ⊕ { p : Fin k × Fin k // p.1 < p.2 }

/-- The graph $H_k$ from Erdős Problem 926.
The center vertex $x$ is adjacent to all spoke vertices $y_i$,
and each pair vertex $z_{ij}$ (for $i < j$) is adjacent to $y_i$ and $y_j$. -/
def graphHk (k : ℕ) : SimpleGraph (HkVertex k) where
  Adj := fun v w => match v, w with
    | Sum.inl (), Sum.inr (Sum.inl _) => True
    | Sum.inr (Sum.inl _), Sum.inl () => True
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inr ⟨(a, b), _⟩) => i = a ∨ i = b
    | Sum.inr (Sum.inr ⟨(a, b), _⟩), Sum.inr (Sum.inl i) => i = a ∨ i = b
    | _, _ => False
  symm := by
    intro v w
    match v, w with
    | Sum.inl (), Sum.inr (Sum.inl _) => intro _; trivial
    | Sum.inr (Sum.inl _), Sum.inl () => intro _; trivial
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inr ⟨(a, b), h⟩) => intro h'; exact h'
    | Sum.inr (Sum.inr ⟨(a, b), h⟩), Sum.inr (Sum.inl i) => intro h'; exact h'
    | Sum.inl (), Sum.inl () => intro h; exact h
    | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => intro h; exact h
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => intro h; exact h
    | Sum.inl (), Sum.inr (Sum.inr _) => intro h; exact h
    | Sum.inr (Sum.inr _), Sum.inl () => intro h; exact h
  loopless := by
    intro v
    match v with
    | Sum.inl () => intro h; exact h
    | Sum.inr (Sum.inl _) => intro h; exact h
    | Sum.inr (Sum.inr ⟨(a, b), h⟩) => nofun

/--
Erdős Problem 926 [Er69b, Er71, Er74c, Er93]:

Let $k \geq 4$. Is it true that $\mathrm{ex}(n; H_k) \ll_k n^{3/2}$, where $H_k$ is the graph on
vertices $x, y_1, \ldots, y_k, z_1, \ldots, z_{\binom{k}{2}}$, where $x$ is adjacent to all $y_i$
and each pair $y_i, y_j$ is adjacent to a unique $z_{ij}$?

The answer is yes, proved by Füredi [Fu91] who showed $\mathrm{ex}(n; H_k) \ll (kn)^{3/2}$,
improved to $\mathrm{ex}(n; H_k) \ll k \cdot n^{3/2}$ by Alon, Krivelevich, and Sudakov [AKS03].
-/
@[category research solved, AMS 5]
theorem erdos_926 : answer(True) ↔
    ∀ (k : ℕ), 4 ≤ k →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (turanNumber (graphHk k) n : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  sorry

end Erdos926
