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
# Erdős Problem 72

*Reference:* [erdosproblems.com/72](https://www.erdosproblems.com/72)

There exists a density-zero set $A$ and a constant $c > 0$ such that every graph with
average degree at least $c$ contains a cycle whose length is in $A$. Proved by
Verstraëte [Ve05]; Liu and Montgomery [LiMo20] showed powers of $2$ work.

[Ve05] Verstraëte, J., *A note on vertex-disjoint cycles*, Combinatorics, Probability and
Computing 14 (2005), 127-143.

[LiMo20] Liu, H. and Montgomery, R., *A solution to Erdős and Hajnal's odd cycle problem*,
Journal of the American Mathematical Society 36 (2023), 1191-1234.
-/

open SimpleGraph

namespace Erdos72

/--
A set $A \subseteq \mathbb{N}$ has natural density zero: for every $\varepsilon > 0$, for all
sufficiently large $n$, $|A \cap \{0, \ldots, n\}| \leq \varepsilon \cdot n$.
-/
def HasDensityZero (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (Set.ncard (A ∩ Set.Iic n) : ℝ) ≤ ε * (n : ℝ)

/--
Is there a set $A \subset \mathbb{N}$ of density $0$ and a constant $c > 0$ such that every graph on
sufficiently many vertices with average degree $\geq c$ contains a cycle whose length is in $A$?

Solved affirmatively by Verstraëte [Ve05] (non-constructive proof).
Liu and Montgomery [LiMo20] proved this holds even when $A$ is the set of powers of $2$.
-/
@[category research solved, AMS 5]
theorem erdos_72 : answer(True) ↔
    ∃ (A : Set ℕ), HasDensityZero A ∧
    ∃ (c : ℝ), c > 0 ∧
    ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ →
      ∀ (G : SimpleGraph (Fin n)) (hd : DecidableRel G.Adj),
        haveI := hd
        2 * (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) →
        ∃ (k : ℕ), k ∈ A ∧ ∃ (v : Fin n), ∃ (p : G.Walk v v), p.IsCycle ∧ p.length = k := by
  sorry

end Erdos72
