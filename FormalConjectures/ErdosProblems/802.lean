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
# Erdős Problem 802

*Reference:* [erdosproblems.com/802](https://www.erdosproblems.com/802)

A conjecture of Ajtai, Erdős, Komlós, and Szemerédi [AEKS81], who proved a
lower bound of $\gg_r (\log \log(t+1) / t) \cdot n$. Shearer [Sh95] improved this to
$\gg_r (\log t / (\log \log(t+1) \cdot t)) \cdot n$. Ajtai, Komlós, and Szemerédi [AKS80]
proved the conjectured bound when $r = 3$. Alon [Al96b] proved the conjectured
bound under the stronger assumption that the induced graph on every vertex
neighbourhood has chromatic number $\leq r - 2$.

[AEKS81] Ajtai, M., Erdős, P., Komlós, J. and Szemerédi, E., _On Turán's theorem for
sparse graphs_. Combinatorica (1981), 313-317.

[AKS80] Ajtai, M., Komlós, J. and Szemerédi, E., _A note on Ramsey numbers_. J. Combin.
Theory Ser. A (1980), 354-360.

[Sh95] Shearer, J. B., _On the independence number of sparse graphs_. Random Structures
Algorithms (1995), 269-271.

[Al96b] Alon, N., _Independence numbers of locally sparse graphs and a Ramsey type
problem_. Random Structures Algorithms (1996), 271-278.
-/

open SimpleGraph Finset

namespace Erdos802

/--
Erdős Problem 802 [AEKS81]:

For every $r \geq 3$, there exists a constant $c > 0$ (depending on $r$) such that
every $K_r$-free graph $G$ on $n$ vertices with average degree $t \geq 2$ contains an
independent set of size at least $c \cdot (\log t / t) \cdot n$.
-/
@[category research open, AMS 5]
theorem erdos_802 : answer(sorry) ↔
    ∀ (r : ℕ), r ≥ 3 →
    ∃ c : ℝ, c > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.CliqueFree r →
    let t : ℝ := (G.averageDegree : ℝ)
    t ≥ 2 →
    ∃ S : Finset (Fin n),
      G.IsIndepSet ↑S ∧
      (S.card : ℝ) ≥ c * (Real.log t / t) * (n : ℝ) := by
  sorry

end Erdos802
