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
# Erdős Problem 533

*Reference:* [erdosproblems.com/533](https://www.erdosproblems.com/533)

Let $\delta > 0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no $K_5$
and at least $\delta n^2$ edges, must $G$ contain a set of $\gg_\delta n$ vertices containing no
triangle? Equivalently, is $\delta_3(5) = 0$? Disproved by Balogh and Lenz [BaLe13].

[BaLe13] Balogh, J. and Lenz, J., _Some exact Ramsey-Turán numbers_, 2013.
-/

open SimpleGraph

namespace Erdos533

/--
Let $\delta > 0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no $K_5$
and at least $\delta n^2$ edges, then $G$ contains a set of $\gg_\delta n$ vertices containing no
triangle.

Equivalently, the conjecture asks whether $\delta_3(5) = 0$, where $\delta_3(5)$ is the
Ramsey-Turán density. This was disproved by Balogh and Lenz [BaLe13], who
showed $\delta_3(5) > 0$. The correct value is $\delta_3(5) = 1/12$.
-/
@[category research solved, AMS 5]
theorem erdos_533 : answer(False) ↔
    ∀ δ : ℝ, 0 < δ →
      ∃ c : ℝ, 0 < c ∧
        ∃ N : ℕ,
          ∀ n : ℕ, N ≤ n →
            ∀ G : SimpleGraph (Fin n),
              G.CliqueFree 5 →
              δ * (n : ℝ) ^ 2 ≤ (G.edgeSet.ncard : ℝ) →
                ∃ S : Finset (Fin n),
                  c * (n : ℝ) ≤ (S.card : ℝ) ∧
                  (G.induce (S : Set (Fin n))).CliqueFree 3 := by
  sorry

end Erdos533
