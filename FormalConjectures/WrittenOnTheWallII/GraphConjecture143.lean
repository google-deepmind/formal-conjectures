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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 143

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 143](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj143):

For a simple connected graph $G$,
$\mathrm{tree}(G) \ge (\mathrm{girth}(G) + 1) / \sigma(G)$,
where $\mathrm{tree}(G)$ is the largest induced tree size, $\mathrm{girth}(G)$
is the length of the shortest cycle, and
$\sigma(G) = G.\mathrm{secondSmallestDegree}$ is the **second-smallest degree**
of $G$'s degree sequence (per WOWII defEntry 65). We state the inequality in
denominator-free form to avoid the $\sigma = 0$ corner case ($n \le 1$).
-/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
"https://github.com/AlperTheKing/formal-conjectures/blob/6aab64fe70c1309463435260d104863dcef93807/FormalConjectures/WrittenOnTheWallII/GraphConjecture143.lean#L44-L71"]
theorem conjecture143 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hσ : 0 < secondSmallestDegree G) :
    (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
  have hnat : G.girth + 1 ≤
      largestInducedTreeSize G * secondSmallestDegree G := by
    by_cases hacyc : G.IsAcyclic
    · have htpos : 0 < largestInducedTreeSize G := one_le_largestInducedTreeSize G
      rw [hacyc.girth_eq_zero]
      exact Nat.mul_pos htpos hσ
    · have hgirth : 3 ≤ G.girth := G.three_le_girth hacyc
      by_cases hσ1 : secondSmallestDegree G = 1
      · obtain ⟨x, y, hxy, hx, hy⟩ :=
          exists_distinct_degree_one_of_secondSmallestDegree_eq_one G
            h.preconnected hσ1
        simpa [hσ1] using
          girth_add_one_le_largestInducedTreeSize_of_two_leaves
            G h hacyc hxy hx hy
      · have hσ2 : 2 ≤ secondSmallestDegree G := by omega
        have htreebound : G.girth - 1 ≤ largestInducedTreeSize G :=
          girth_sub_one_le_largestInducedTreeSize G hacyc
        calc
          G.girth + 1 ≤ 2 * (G.girth - 1) := by omega
          _ ≤ 2 * largestInducedTreeSize G :=
            Nat.mul_le_mul_left 2 htreebound
          _ = largestInducedTreeSize G * 2 := by omega
          _ ≤ largestInducedTreeSize G * secondSmallestDegree G :=
            Nat.mul_le_mul_left _ hσ2
  exact_mod_cast hnat

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The second-smallest degree is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : 0 ≤ secondSmallestDegree G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture143
