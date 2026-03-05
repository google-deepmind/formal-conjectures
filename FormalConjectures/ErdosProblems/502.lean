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

[Er61] Erdős, P., *Számelmélet és gráfelmélet* (1961).

[BBS83] Bannai, E., Bannai, E., and Stanton, D., *An upper bound for the cardinality of an
$s$-distance subset in real Euclidean space II*, Combinatorica (1983).

[PePo21] Petrov, F. and Pohoata, C., *The answer to a question of Naimark and Sternfeld on
two-distance sets*, European J. Combin. (2021).
-/

namespace Erdos502

/--
A finite set of points in $\mathbb{R}^n$ is a two-distance set if there are exactly
two distinct positive real numbers that occur as distances between pairs
of distinct points.
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

end Erdos502
