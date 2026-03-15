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

Give an asymptotic formula for $R(3,k)$. Prize: $250.

$R(3,k)$ is the Ramsey number: the minimum $N$ such that every simple graph
on $N$ vertices contains either a triangle ($3$-clique) or an independent set
of size $k$ (equivalently, a $k$-clique in the complement).

It is known that for some constant $c > 0$ and large $k$:
$$
  (c + o(1)) \frac{k^2}{\log k} \leq R(3,k) \leq (1 + o(1)) \frac{k^2}{\log k}
$$

The upper bound is due to Shearer [Sh83], improving Ajtai–Komlós–Szemerédi
[AKS80]. The lower bound has been progressively improved: Kim [Ki95] showed
$c \geq 1/162$, Fiz Pontiveros–Griffiths–Morris [PGM20] and Bohman–Keevash
[BoKe21] improved this to $c \geq 1/4$, Campos–Jenssen–Michelen–Sahasrabudhe
[CJMS25] to $c \geq 1/3$, and Hefty–Horn–King–Pfender [HHKP25] to
$c \geq 1/2$. The conjectured asymptotic is
$R(3,k) \sim \frac{1}{2} \frac{k^2}{\log k}$.

Related problems: 544, 986, 1013. OEIS: [A000791](https://oeis.org/A000791).

[AKS80] Ajtai, M., Komlós, J. and Szemerédi, E., _A note on Ramsey numbers_.
J. Combin. Theory Ser. A **29** (1980), 354-360.

[Sh83] Shearer, J. B., _A note on the independence number of triangle-free
graphs_. Discrete Math. **46** (1983), 83-87.

[Ki95] Kim, J. H., _The Ramsey number R(3,t) has order of magnitude t²/log t_.
Random Structures and Algorithms (1995), 173-207.

[PGM20] Fiz Pontiveros, G., Griffiths, S. and Morris, R., _The triangle-free
process and the Ramsey number R(3,k)_. Mem. Amer. Math. Soc. (2020).

[BoKe21] Bohman, T. and Keevash, P., _Dynamic concentration of the
triangle-free process_. Random Structures Algorithms (2021), 221-293.

[CJMS25] Campos, M., Jenssen, M., Michelen, M. and Sahasrabudhe, J.,
_A new lower bound for the Ramsey numbers R(3,k)_. arXiv:2505.13371 (2025).

[HHKP25] Hefty, L., Horn, P., King, R. and Pfender, F., _Improving R(3,k) in
just two bites_. arXiv:2510.19718 (2025).

[Er61] Erdős, P. (1961). [Er71] Erdős, P. (1971). [Er78] Erdős, P. (1978).
[Er90b] Erdős, P. (1990). [Er93] Erdős, P. (1993). [Er97c] Erdős, P. (1997).
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

/--
Erdős Problem 165 — conjectured value $c = 1/2$:

$R(3,k) \sim \frac{1}{2} \frac{k^2}{\log k}$, i.e., for all $\varepsilon > 0$
and all sufficiently large $k$:
$$
  (1/2 - \varepsilon) \cdot \frac{k^2}{\log k} \leq R(3,k) \leq (1/2 + \varepsilon) \cdot \frac{k^2}{\log k}.
$$
-/
@[category research open, AMS 5]
theorem erdos_165_conjectured_value :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      (1 / 2 - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ) ∧
      (ramseyR3 k : ℝ) ≤ (1 / 2 + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) := by
  sorry

end Erdos165
