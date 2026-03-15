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
# Erdős Problem 502

*Reference:* [erdosproblems.com/502](https://www.erdosproblems.com/502)

Erdős asked (after Coxeter): what is the maximum size of a subset of $\mathbb{R}^n$
with only two distinct pairwise distances? Bannai, Bannai, and Stanton proved an
upper bound of $\binom{n+2}{2}$.

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. **6**
(1961), 221–254. (p. 244)

[BBS83] Bannai, E., Bannai, E., and Stanton, D., _An upper bound for the cardinality of an
$s$-distance subset in real Euclidean space. II_. Combinatorica (1983), 147–152.

[PePo21] Petrov, F. and Pohoata, C., _A remark on sets with few distances in $\mathbb{R}^d$_.
Proc. Amer. Math. Soc. (2021), 569–571.

See also Problem 1089 for the general $s$-distance version of this question.

OEIS: [A027627](https://oeis.org/A027627)
-/

namespace Erdos502

/--
A finite set of points in $\mathbb{R}^n$ is a two-distance set if there are exactly
two distinct positive real numbers that occur as distances between pairs
of distinct points. (Positivity is automatic since `dist x y > 0` for `x ≠ y`
in Euclidean space.)
-/
noncomputable def IsTwoDistanceSet {n : ℕ} (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  Set.ncard {d : ℝ | ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ d = dist x y} = 2

/--
Erdős Problem 502 — Bannai–Bannai–Stanton Upper Bound [Er61] [BBS83]:

Any two-distance set $A \subseteq \mathbb{R}^n$ has at most $\binom{n+2}{2}$ elements.
A simpler proof was given by Petrov and Pohoata [PePo21]. The best known lower bound
is $\binom{n+1}{2}$ via a construction of Alweiss.
-/
@[category research solved, AMS 5 52]
theorem erdos_502
    (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin n)))
    (hA : IsTwoDistanceSet A) :
    A.card ≤ Nat.choose (n + 2) 2 := by
  sorry

/--
Erdős Problem 502 — Lower Bound (Alweiss construction):

There exists a two-distance set in $\mathbb{R}^n$ of size $\binom{n+1}{2}$.
This is the best known lower bound, complementing the Bannai–Bannai–Stanton
upper bound of $\binom{n+2}{2}$. See also Problem 503.
-/
@[category research solved, AMS 5 52]
theorem erdos_502_lower
    (n : ℕ) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsTwoDistanceSet A ∧ A.card = Nat.choose (n + 1) 2 := by
  sorry

end Erdos502
