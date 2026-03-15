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
# Erdős Problem 1159

*Reference:* [erdosproblems.com/1159](https://www.erdosproblems.com/1159)

Determine whether there exists a constant $C > 1$ such that every finite projective plane
has a blocking set where no line is hit more than $C$ times. A blocking set is a set of
points that meets every line.

Erdős [Er81] posed the stronger question for all pairwise balanced block designs, not just
projective planes. See also Problem #664 for a related (stronger) variant.

Erdős, Silverman, and Stein [ESS83] proved this is true with
$|S \cap \ell| \ll \log n$ for all lines $\ell$ (where $n$ is the order of the projective
plane).

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
Combinatorica 1 (1981), 25–42.

[ESS83] Erdős, P., Silverman, R., Stein, A., _Intersection properties of families
containing sets of nearly the same size_, Ars Combinatoria (1983), 247–259.

[Va99] Vardy, A.
-/

open Configuration Classical Finset

namespace Erdos1159

/--
Erdős Problem 1159 [Va99, 4.70]:

Does there exist an absolute constant $C > 1$ such that every finite projective plane
has a set of points $S$ meeting every line in at least $1$ and at most $C$ points?
-/
@[category research open, AMS 5 51]
theorem erdos_1159 : answer(sorry) ↔
    ∃ C : ℕ, 1 < C ∧
      ∀ (P L : Type) [Membership P L] [Fintype P] [Fintype L]
        [Configuration.ProjectivePlane P L],
        ∃ S : Finset P,
          ∀ l : L, 1 ≤ (S.filter (fun p => p ∈ l)).card ∧
                    (S.filter (fun p => p ∈ l)).card ≤ C := by
  sorry

/--
Erdős–Silverman–Stein [ESS83] proved that every finite projective plane of order $n$ has a
blocking set $S$ such that $|S \cap \ell| \ll \log n$ for all lines $\ell$.
-/
@[category research solved, AMS 5 51]
theorem erdos_1159_ess_log_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P L : Type) [Membership P L] [Fintype P] [Fintype L]
        (pp : Configuration.ProjectivePlane P L),
        ∃ S : Finset P,
          ∀ l : L, 1 ≤ (S.filter (fun p => p ∈ l)).card ∧
                    (S.filter (fun p => p ∈ l)).card ≤ ⌈C * Real.log pp.order⌉₊ := by
  sorry

end Erdos1159
