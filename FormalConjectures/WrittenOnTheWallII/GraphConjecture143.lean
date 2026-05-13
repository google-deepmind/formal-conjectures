/-
Copyright 2025 The Formal Conjectures Authors.

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
# Written on the Wall II - Conjecture 143

**Verbatim statement (WOWII #143, status O):**
> If G is a simple connected graph, then tree(G) ≥ (girth + 1)/σ(G)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj143


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **second-smallest degree** of `G`'s degree sequence — DeLaVina's `σ(G)`
per the WOWII definitions popup (defEntry 65): "order the degree sequence in
nondecreasing order `d₁ ≤ d₂ ≤ … ≤ dₙ`, the second smallest degree of the
sequence is the 2nd entry". For graphs with `n ≤ 1` we conventionally
return `0`. -/
noncomputable def secondSmallestDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (degreeSequence G).getD 1 0

/--
WOWII [Conjecture 143](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj143)
(status O):

For a simple connected graph `G`,
`tree(G) ≥ (girth(G) + 1) / σ(G)`,
where `tree(G)` is the largest induced tree size, `girth(G)` is the length
of the shortest cycle, and `σ(G)` is the **second-smallest degree** of `G`'s
degree sequence (per WOWII defEntry 65). We state the inequality in
denominator-free form to avoid the `σ = 0` corner case (n ≤ 1).
-/
@[category research open, AMS 5]
theorem conjecture143 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hσ : 0 < secondSmallestDegree G) :
    (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The second-smallest degree is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : 0 ≤ secondSmallestDegree G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture143
