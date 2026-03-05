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
# Erdős Problem 911

Is there a function $f$ with $f(x)/x \to \infty$ such that, for all sufficiently large $C$,
every graph $G$ with $n$ vertices and at least $Cn$ edges satisfies
$\hat{R}(G) > f(C) \cdot |E(G)|$?

*Reference:* [erdosproblems.com/911](https://www.erdosproblems.com/911)

[Er82e] Erdős, P., _Problems and results in graph theory_. (1982), p. 78.
-/

open SimpleGraph

namespace Erdos911

/-- The size Ramsey number $\hat{R}(G)$: the minimum number of edges in a graph $H$
    that is Ramsey for $G$.

    A graph $H$ on $N$ vertices is Ramsey for $G$ if every 2-coloring of the edges
    of $H$ (represented as a symmetric function $c : \operatorname{Fin} N \to
    \operatorname{Fin} N \to \operatorname{Bool}$) contains a monochromatic copy of
    $G$, i.e., an injective map $f$ from the vertices of $G$ into
    $\operatorname{Fin} N$ that preserves adjacency in $H$ and maps all edges to the
    same color. -/
noncomputable def sizeRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ (N : ℕ) (H : SimpleGraph (Fin N)),
    Nat.card H.edgeSet = m ∧
    ∀ (c : Fin N → Fin N → Bool),
      (∀ i j, c i j = c j i) →
      ∃ (b : Bool) (f : V → Fin N),
        Function.Injective f ∧
        (∀ u v, G.Adj u v → H.Adj (f u) (f v)) ∧
        (∀ u v, G.Adj u v → c (f u) (f v) = b)}

/--
Erdős Problem #911 [Er82e, p.78]:

Is there a function $f : \mathbb{N} \to \mathbb{N}$ with $f(x)/x \to \infty$ as
$x \to \infty$ such that, for all sufficiently large $C$, if $G$ is any graph with
$n$ vertices and at least $C \cdot n$ edges then
$\hat{R}(G) > f(C) \cdot |E(G)|$?
-/
@[category research open, AMS 5]
theorem erdos_911 :
    answer(sorry) ↔
    ∃ f : ℕ → ℕ,
      -- f(x)/x → ∞ as x → ∞
      (∀ M : ℕ, ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ → f x ≥ M * x) ∧
      -- For all large C, the bound holds
      ∃ C₀ : ℕ, ∀ C : ℕ, C ≥ C₀ →
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
          Nat.card G.edgeSet ≥ C * n →
          sizeRamseyNumber G > f C * Nat.card G.edgeSet := by
  sorry

end Erdos911
