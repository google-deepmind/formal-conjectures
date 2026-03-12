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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 72

*Reference:* [erdosproblems.com/72](https://www.erdosproblems.com/72)

There exists a density-zero set $A$ and a constant $c > 0$ such that every graph with
average degree at least $c$ contains a cycle whose length is in $A$. Proved by
Verstraëte [Ve05]; Liu and Montgomery [LiMo20] showed powers of $2$ work.
Erdős was "almost certain" that powers of $2$ would not work, and offered \$100 for a solution.

See also Problem 71.

[Bo77] Bollobás, B., *Cycles modulo k*. Bull. London Math. Soc. 9 (1977), 97-98.

[Er94b] Erdős, P., _Some old and new problems in various branches of combinatorics_.
Math. Pannon. (1994), 261-269.

[Er95] Erdős, P., _Some recent problems and results in graph theory_.
Discrete Math. 164 (1997), 81–85.

[Er97b] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proceedings of the International Conference on Discrete Mathematics (ICDM) (1997).

[Er97c] Erdős, P. (1997).

[Ve05] Verstraëte, J., *A note on vertex-disjoint cycles*, Combinatorics, Probability and
Computing 14 (2005), 127-143.

[LiMo20] Liu, H. and Montgomery, R., *A solution to Erdős and Hajnal's odd cycle problem*,
Journal of the American Mathematical Society 36 (2023), 1191-1234.
-/

open SimpleGraph

namespace Erdos72

/--
Is there a set $A \subset \mathbb{N}$ of density $0$ and a constant $c > 0$ such that every graph on
sufficiently many vertices with average degree $\geq c$ contains a cycle whose length is in $A$?

Solved affirmatively by Verstraëte [Ve05] (non-constructive proof).
Liu and Montgomery [LiMo20] proved this holds even when $A$ is the set of powers of $2$.
-/
@[category research solved, AMS 5]
theorem erdos_72 : answer(True) ↔
    ∃ (A : Set ℕ), A.HasDensity 0 ∧
    ∃ (c : ℝ), c > 0 ∧
    ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ →
      ∀ (G : SimpleGraph (Fin n)) (hd : DecidableRel G.Adj),
        haveI := hd
        2 * (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) →
        ∃ (k : ℕ), k ∈ A ∧ ∃ (v : Fin n), ∃ (p : G.Walk v v), p.IsCycle ∧ p.length = k := by
  sorry

/--
Liu–Montgomery powers-of-2 variant [LiMo20]: There exists $c > 0$ such that every graph on
sufficiently many vertices with average degree $\geq c$ contains a cycle whose length is a
power of $2$. This is a strictly stronger result than `erdos_72`, giving an explicit
density-zero set.
-/
@[category research solved, AMS 5]
theorem erdos_72_powers_of_two :
    ∃ (c : ℝ), c > 0 ∧
    ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ →
      ∀ (G : SimpleGraph (Fin n)) (hd : DecidableRel G.Adj),
        haveI := hd
        2 * (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) →
        ∃ (k : ℕ), (∃ m : ℕ, k = 2 ^ m) ∧
          ∃ (v : Fin n), ∃ (p : G.Walk v v), p.IsCycle ∧ p.length = k := by
  sorry

end Erdos72
