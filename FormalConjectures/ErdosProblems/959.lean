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
# Erdős Problem 959

*Reference:* [erdosproblems.com/959](https://www.erdosproblems.com/959)

Let $A \subset \mathbb{R}^2$ be a set of size $n$ and let $\{d_1, \ldots, d_k\}$
be the set of distinct distances determined by $A$. Let $f(d)$ be the number of
times the distance $d$ is determined (as an unordered pair), and suppose the $d_i$
are ordered such that $f(d_1) \geq f(d_2) \geq \cdots \geq f(d_k)$.

Estimate $\max (f(d_1) - f(d_2))$, where the maximum is taken over all $A$ of
size $n$.

[Er84d] Erdős, P., *Some old and new problems on combinatorial geometry*.

[CDL25] Clemen, F., Dumitrescu, A., and Liu, J., *On the gap between the most frequent and
second most frequent distances*.
-/

open Classical

namespace Erdos959

/-- The set of distinct distances determined by a finite point set in $\mathbb{R}^2$. -/
noncomputable def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)

/-- The multiplicity of distance $d$ in $A$: the number of unordered pairs at distance $d$. -/
noncomputable def distMultiplicity (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card / 2

/--
**Erdős Problem 959** [Er84d]:

For any sufficiently large $n$, there exists a set $A$ of $n$ points in $\mathbb{R}^2$
such that the gap between the most frequent and every other distance multiplicity
is at least $c \cdot n \cdot \log n$ for some absolute constant $c > 0$.

Equivalently, $\max_A (f(d_1) - f(d_2)) \gg n \log n$ where $f(d_1) \geq f(d_2)$
are the two largest distance multiplicities.

This lower bound was proved by Clemen, Dumitrescu, and Liu [CDL25].
-/
@[category research solved, AMS 52]
theorem erdos_959 :
    ∃ c : ℝ, c > 0 ∧ ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧
        ∃ d₁ ∈ distinctDistances A,
          (∀ d ∈ distinctDistances A, distMultiplicity A d ≤ distMultiplicity A d₁) ∧
          ∀ d₂ ∈ distinctDistances A, d₂ ≠ d₁ →
            (distMultiplicity A d₁ : ℝ) - (distMultiplicity A d₂ : ℝ) ≥
              c * (n : ℝ) * Real.log (n : ℝ) := by
  sorry

end Erdos959
