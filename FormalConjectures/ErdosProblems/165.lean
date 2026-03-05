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
# Erdős Problem 165

*Reference:* [erdosproblems.com/165](https://www.erdosproblems.com/165)

Give an asymptotic formula for $R(3,k)$.

$R(3,k)$ is the Ramsey number: the minimum $N$ such that every simple graph
on $N$ vertices contains either a triangle ($3$-clique) or an independent set
of size $k$ (equivalently, a $k$-clique in the complement).

It is known that for some constant $c > 0$ and large $k$:
$$
  (c + o(1)) \frac{k^2}{\log k} \leq R(3,k) \leq (1 + o(1)) \frac{k^2}{\log k}
$$

The upper bound is due to Shearer [Sh83], improving Ajtai–Komlós–Szemerédi
[AKS80]. The lower bound constant has been improved to $c \geq 1/2$ by
Hefty–Horn–King–Pfender [HHKP25]. The conjectured asymptotic is
$R(3,k) \sim \frac{1}{2} \frac{k^2}{\log k}$.

[Sh83] Shearer, J. B., _A note on the independence number of triangle-free
graphs_. Discrete Mathematics (1983).

[AKS80] Ajtai, M., Komlós, J. and Szemerédi, E., _A note on Ramsey numbers_.
Journal of Combinatorial Theory, Series A (1980).

[HHKP25] Hefty, L., Horn, P., King, R. and Pfender, F., _On the Ramsey number
$R(3,t)$_. (2025).

[Er61] Erdős, P. (1961). [Er71] Erdős, P. (1971). [Er90b] Erdős, P. (1990).
[Er93] Erdős, P. (1993). [Er97c] Erdős, P. (1997).
-/

open SimpleGraph Real

namespace Erdos165

/-- The Ramsey number $R(3,k)$: the minimum $N$ such that every simple graph
on $N$ vertices contains either a triangle ($3$-clique) or an independent
set of size $k$ (a $k$-clique in the complement). -/
noncomputable def ramseyR3 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree k}

/--
Erdős Conjecture (Problem 165) [Er61, Er71, Er90b, Er93, Er97c]:

There exists a constant $c > 0$ such that $R(3,k) \sim c \cdot k^2 / \log k$, i.e.,
for all $\varepsilon > 0$ and all sufficiently large $k$:
$$
  (c - \varepsilon) \cdot \frac{k^2}{\log k} \leq R(3,k) \leq (c + \varepsilon) \cdot \frac{k^2}{\log k}.
$$

The conjectured value is $c = 1/2$.
-/
@[category research open, AMS 5]
theorem erdos_165 : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      (c - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ) ∧
      (ramseyR3 k : ℝ) ≤ (c + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) := by
  sorry

end Erdos165
