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
# Erdős Problem 988

*Reference:* [erdosproblems.com/988](https://www.erdosproblems.com/988)

If $P \subseteq S^2$ is a subset of the unit sphere then define the discrepancy
$$D(P) = \max_C \left| |C \cap P| - \alpha_C |P| \right|,$$
where the maximum is taken over all spherical caps $C$, and $\alpha_C$ is the
appropriately normalised measure of $C$.

Is it true that $\min_{|P|=n} D(P) \to \infty$ as $n \to \infty$?

Roth [Ro54] proved that the answer is yes if the sphere is replaced by a square.
This was proved (in any number of dimensions) by Schmidt [Sc69b].

[Er64b] Erdős, P., *On some problems in number theory*, 1964.

[Ro54] Roth, K. F., *On irregularities of distribution.* Mathematika **1**
(1954), 73–79.

[Sc69b] Schmidt, W. M., *Irregularities of distribution. IV.* Invent. Math. **7**
(1969), 55–82.
-/

open Classical

namespace Erdos988

/--
Erdős Problem 988 [Er64b]:

For every $M > 0$, there exists $N_0$ such that for every finite set $P$ of points
on the unit sphere $S^2$ in $\mathbb{R}^3$ with $|P| \geq N_0$, there exists a spherical cap
$C(v,t) = \{x \in S^2 : \langle x, v \rangle \geq t\}$ (with $v$ a unit vector and
$t \in [-1,1]$) such that the discrepancy
$\left||C(v,t) \cap P| - \frac{1-t}{2} \cdot |P|\right| \geq M$.

Here $\frac{1-t}{2}$ is the normalised surface area measure of the cap $C(v,t)$ on $S^2$.
-/
@[category research solved, AMS 11 52]
theorem erdos_988 :
    answer(True) ↔
    ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ (P : Finset (EuclideanSpace ℝ (Fin 3))),
      (∀ p ∈ P, ‖p‖ = 1) →
      P.card ≥ N₀ →
      ∃ (v : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
        ‖v‖ = 1 ∧ -1 ≤ t ∧ t ≤ 1 ∧
        |((P.filter (fun x => @inner ℝ _ _ x v ≥ t)).card : ℝ) -
          (1 - t) / 2 * (P.card : ℝ)| ≥ M := by
  sorry

end Erdos988
