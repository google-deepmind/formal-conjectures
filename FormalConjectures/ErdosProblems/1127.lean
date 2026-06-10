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
# Erdős Problem 1127

*Reference:* [erdosproblems.com/1127](https://www.erdosproblems.com/1127)

Can $\mathbb{R}^n$ be decomposed into countably many sets such that within each
set all the pairwise distances are distinct?

The answer is independent of ZFC.

Assuming the continuum hypothesis, the answer is yes: Erdős and Kakutani [ErKa43]
proved that the continuum hypothesis is equivalent to the statement that
$\mathbb{R}$ is the union of countably many sets each linearly independent over
$\mathbb{Q}$ (which gives the case $n = 1$); Davies [Da72] proved the case
$n = 2$, and Kunen [Ku87] proved it for all $n$.

Conversely, some hypothesis beyond ZFC is necessary: Erdős and Hajnal showed
that if the continuum hypothesis fails, then in any decomposition of
$\mathbb{R}$ into finitely many sets, one of the sets contains four points
determining only four distances (in particular, with a repeated distance).

*References:*
- [ErKa43] Erdős, P. and Kakutani, S., _On non-denumerable graphs_,
  Bull. Amer. Math. Soc. 49 (1943), 457–461.
- [Da72] Davies, R. O., _Partitioning the plane into denumerably many sets
  without repeated distances_, Proc. Cambridge Philos. Soc. 72 (1972), 179–183.
- [Ku87] Kunen, K., _Partitioning Euclidean space_,
  Math. Proc. Cambridge Philos. Soc. 102 (1987), 379–383.
- [Er81b] Erdős, P., _Problems and results in combinatorial analysis and
  combinatorial number theory_ (1981), p. 31.
-/

open Cardinal
open scoped Cardinal

namespace Erdos1127

/--
A set $A$ in a metric space has **pairwise distinct distances** if any two pairs of
distinct points of $A$ realising the same distance are equal as unordered pairs:
whenever $x, y, z, w \in A$ with $x \neq y$, $z \neq w$ and
$d(x, y) = d(z, w)$, we have $\{x, y\} = \{z, w\}$.
-/
def PairwiseDistinctDistances {X : Type*} [MetricSpace X] (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ w ∈ A,
    x ≠ y → z ≠ w → dist x y = dist z w → (x = z ∧ y = w) ∨ (x = w ∧ y = z)

/--
`Decomposable n` states that $\mathbb{R}^n$ can be decomposed into countably many
sets each of which has pairwise distinct distances.
-/
def Decomposable (n : ℕ) : Prop :=
  ∃ A : ℕ → Set (EuclideanSpace ℝ (Fin n)),
    (⋃ i, A i) = Set.univ ∧ ∀ i, PairwiseDistinctDistances (A i)

/--
**Erdős Problem 1127:**
Can $\mathbb{R}^n$ be decomposed into countably many sets such that all the
pairwise distances within each set are distinct?

The answer is independent of ZFC: it is yes under the continuum hypothesis
(Kunen [Ku87], building on Erdős–Kakutani [ErKa43] for $n = 1$ and
Davies [Da72] for $n = 2$), while Erdős and Hajnal showed that if the continuum
hypothesis fails then even a decomposition of $\mathbb{R}$ into finitely many
such sets is impossible.
-/
@[category research solved, AMS 3 52]
theorem erdos_1127 : answer(sorry) ↔ ∀ n : ℕ, Decomposable n := by
  sorry

/--
Kunen [Ku87] proved that, assuming the continuum hypothesis, $\mathbb{R}^n$ can be
decomposed into countably many sets within each of which all pairwise distances
are distinct, for every $n$.
-/
@[category research solved, AMS 3 52]
theorem erdos_1127.variants.kunen (hCH : 𝔠 = ℵ_ 1) : ∀ n, Decomposable n := by
  sorry

/--
Davies [Da72] proved that, assuming the continuum hypothesis, the plane
$\mathbb{R}^2$ can be decomposed into countably many sets without repeated
distances.
-/
@[category research solved, AMS 3 52]
theorem erdos_1127.variants.davies (hCH : 𝔠 = ℵ_ 1) : Decomposable 2 := by
  sorry

/--
Erdős and Kakutani [ErKa43] proved that the continuum hypothesis is equivalent
to the statement that $\mathbb{R}$ is the union of countably many sets, each of
which is linearly independent over $\mathbb{Q}$. In particular, the continuum
hypothesis implies the case $n = 1$ of Erdős Problem 1127.
-/
@[category research solved, AMS 3 52]
theorem erdos_1127.variants.erdos_kakutani :
    (𝔠 = ℵ_ 1) ↔ ∃ A : ℕ → Set ℝ,
      (⋃ i, A i) = Set.univ ∧ ∀ i, LinearIndepOn ℚ id (A i) := by
  sorry

/--
Erdős and Hajnal proved that if the continuum hypothesis fails, then in any
decomposition of $\mathbb{R}$ into finitely many sets, one of the sets contains
four points determining only four distances. In particular, $\mathbb{R}$ cannot
be decomposed into finitely many sets within each of which all pairwise
distances are distinct.
-/
@[category research solved, AMS 3 52]
theorem erdos_1127.variants.erdos_hajnal (hCH : ℵ_ 1 < 𝔠) :
    ¬ ∃ (k : ℕ) (A : Fin k → Set ℝ),
      (⋃ i, A i) = Set.univ ∧ ∀ i, PairwiseDistinctDistances (A i) := by
  sorry

/--
The case $n = 0$ is trivially true: $\mathbb{R}^0$ is a single point, so the
distinct-distance condition holds vacuously.
-/
@[category test, AMS 52]
theorem erdos_1127.variants.decomposable_zero : Decomposable 0 := by
  refine ⟨fun _ => Set.univ, Set.iUnion_const _, fun i x _ y _ z _ w _ hxy _ _ => ?_⟩
  exact absurd (Subsingleton.elim x y) hxy

end Erdos1127
