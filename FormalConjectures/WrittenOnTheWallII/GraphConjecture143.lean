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

The proof splits into the acyclic case and two cyclic cases. For an acyclic
graph the girth is zero. If $\sigma \ge 2$, deleting two consecutive edges from
a shortest cycle leaves an induced tree on $\mathrm{girth}(G)-1$ vertices, and
the factor $\sigma \ge 2$ yields the required inequality. If $\sigma = 1$,
there are two degree-one vertices. A maximal induced tree containing them must
have an external vertex with two attachments; those attachments create a cycle
whose length forces the tree to contain at least $\mathrm{girth}(G)+1$ vertices.
-/
@[category research solved, AMS 5,
  formal_proof using formal_conjectures at "https://github.com/DomTheDeveloper/formal-conjectures/blob/693e9aa206a5c6c98598aa4e6e5f3db0994a79b7/FormalConjectures/WrittenOnTheWallII/Proofs/GraphConjecture143.lean"]
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
