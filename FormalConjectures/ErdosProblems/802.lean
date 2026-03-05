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
-/

open SimpleGraph Finset

namespace Erdos802

/-- The average degree of a finite simple graph on `Fin n`. -/
noncomputable def avgDegree {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  (∑ v : Fin n, (G.degree v : ℝ)) / (n : ℝ)

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
    avgDegree G ≥ 2 →
    ∃ S : Finset (Fin n),
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v) ∧
      (S.card : ℝ) ≥ c * (Real.log (avgDegree G) / avgDegree G) * (n : ℝ) := by
  sorry

end Erdos802
