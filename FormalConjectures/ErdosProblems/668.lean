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
import FormalConjecturesForMathlib.Geometry.Metric
import FormalConjecturesForMathlib.Geometry.«2d»

/-!
# Erdős Problem 668

*Reference:* [erdosproblems.com/668](https://www.erdosproblems.com/668)

Is it true that the number of incongruent sets of $n$ points in $\mathbb{R}^2$ which
maximise the number of unit distances tends to infinity as $n \to \infty$?
Is it always $> 1$ for $n > 3$?

In fact this is $= 1$ also for $n = 4$, the unique example given by two
equilateral triangles joined by an edge.

The actual maximal number of unit distances is the subject of problem #90.

[Er97f] Erdős, P., _Some of my favourite problems which recently have been solved_.
Proceedings of the International Conference on Set-theoretic Topology and its Applications
(Matsuyama, 1994) (1997), 59-79.

[EHSVZ25] Engel, P., Hammond-Lee, O., Su, Y., Varga, D., Zsámboki, P., _Diverse beam search
to find densest-known planar unit distance graphs_. arXiv:2406.15317 (2025).

[AMP25] Alexeev, B., Mixon, D., Parshall, H., _The Erdős unit distance problem for small
point sets_. arXiv:2412.11914 (2025).
-/

open scoped EuclideanGeometry

namespace Erdos668

/-- The maximum number of unit distance pairs among all $n$-point
    sets in $\mathbb{R}^2$. -/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset ℝ²,
    P.card = n ∧ unitDistNum P = k}

/-- Two finite point sets in $\mathbb{R}^2$ are congruent if there is a distance-preserving
    map of $\mathbb{R}^2$ sending one onto the other. -/
def AreCongruent
    (P Q : Finset ℝ²) : Prop :=
  ∃ f : ℝ² → ℝ²,
    (∀ x y, dist (f x) (f y) = dist x y) ∧
    f '' (↑P : Set ℝ²) = ↑Q

/--
**Erdős Problem 668** [Er97f]:

Is it true that the number of incongruent $n$-point sets in $\mathbb{R}^2$ maximising the number of
unit distances tends to infinity as $n \to \infty$?

Formulated as: for every $M$, there exists $N$ such that for all $n \ge N$, there
exist $M$ pairwise non-congruent $n$-point sets each achieving the maximum
unit distance count.
-/
@[category research open, AMS 5 52]
theorem erdos_668 :
    answer(sorry) ↔
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (Ps : Fin M → Finset ℝ²),
        (∀ i, (Ps i).card = n ∧
              unitDistNum (Ps i) = maxUnitDistances n) ∧
        (∀ i j, i ≠ j → ¬AreCongruent (Ps i) (Ps j)) := by
  sorry

/--
**Erdős Problem 668, Part 2** [Er97f]:

For every $n > 3$, do there exist at least two incongruent $n$-point sets in $\mathbb{R}^2$
achieving the maximum number of unit distances?

Note: the additional commentary on the problem states that the count of
incongruent maximisers is in fact $= 1$ for $n = 4$, so this part of the
conjecture may be false as stated. Computational evidence [EHSVZ25] [AMP25]
suggests uniqueness (up to graph isomorphism, which implies uniqueness up to
congruence) for $5 \le n \le 21$.
-/
@[category research open, AMS 5 52]
theorem erdos_668.variants.part2 :
    answer(sorry) ↔
    ∀ (n : ℕ), n > 3 →
    ∃ (P Q : Finset ℝ²),
      P.card = n ∧ Q.card = n ∧
      unitDistNum P = maxUnitDistances n ∧
      unitDistNum Q = maxUnitDistances n ∧
      ¬AreCongruent P Q := by
  sorry

end Erdos668
