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
# Erdős Problem 904

If $G$ is a graph with $n$ vertices and more than $n^2/4$ edges, then $G$ contains a
triangle on vertices $x, y, z$ such that $d(x) + d(y) + d(z) \geq 3n/2$.

*Reference:* [erdosproblems.com/904](https://www.erdosproblems.com/904)

[Ed78] Edwards, C. S., _Recent results on the Bollobás-Erdős conjecture_. (1978)
-/

open SimpleGraph

namespace Erdos904

/--
Bollobás-Erdős conjecture (proved by Edwards [Ed78]):
If $G$ is a graph with $n$ vertices and more than $n^2/4$ edges, then $G$ contains a
triangle on vertices $x, y, z$ such that $d(x) + d(y) + d(z) \geq 3n/2$.
-/
@[category research solved, AMS 5]
theorem erdos_904 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (n : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) →
      ∃ x y z : Fin n, G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
        (G.degree x + G.degree y + G.degree z : ℝ) ≥ 3 / 2 * (n : ℝ) := by
  sorry

end Erdos904
