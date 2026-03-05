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
# Erdős Problem 553

*Reference:* [erdosproblems.com/553](https://www.erdosproblems.com/553)

Let $R(3,3,n)$ denote the smallest integer $m$ such that if we $3$-colour the edges
of $K_m$ then there is either a monochromatic triangle in one of the first two
colours or a monochromatic $K_n$ in the third colour. Define $R(3,n)$ similarly
but with two colours.

A problem of Erdős and Sós [ErSo80]. This was solved by Alon and Rödl [AlRo05], who
showed $R(3,3,n) \asymp n^3 (\log n)^{O(1)}$, recalling that Shearer [Sh83] showed
$R(3,n) \ll n^2 / \log n$.
-/

open SimpleGraph

namespace Erdos553

/-- The Ramsey number $R(3,n)$: the minimum $N$ such that every $2$-colouring of
the edges of $K_N$ yields either a monochromatic triangle in colour $1$ or
a monochromatic $K_n$ in colour $2$. Equivalently, every simple graph on $N$
vertices contains a $3$-clique or its complement contains an $n$-clique. -/
noncomputable def ramseyR3 (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree n}

/-- The Ramsey number $R(3,3,n)$: the minimum $N$ such that every $3$-colouring of
the edges of $K_N$ yields either a monochromatic triangle in one of the
first two colours or a monochromatic $K_n$ in the third colour.

A $3$-colouring is modelled by two edge-disjoint graphs $G_1$, $G_2$ (the first
two colour classes); the third colour class is the complement $(G_1 \sqcup G_2)^c$. -/
noncomputable def ramseyR33 (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G₁ G₂ : SimpleGraph (Fin N)),
    Disjoint G₁ G₂ →
    ¬G₁.CliqueFree 3 ∨ ¬G₂.CliqueFree 3 ∨ ¬(G₁ ⊔ G₂)ᶜ.CliqueFree n}

/--
Erdős Problem 553 [ErSo80]:

$$R(3,3,n) / R(3,n) \to \infty$$

as $n \to \infty$.

Formulated as: for every positive real $C$, there exists $N_0$ such that for all
$n \ge N_0$ we have $R(3,3,n) \ge C \cdot R(3,n)$.
-/
@[category research solved, AMS 5]
theorem erdos_553 :
    ∀ C : ℝ, C > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C * (ramseyR3 n : ℝ) ≤ (ramseyR33 n : ℝ) := by
  sorry

end Erdos553
