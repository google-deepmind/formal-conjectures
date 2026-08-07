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
# Erdős Problem 217

*Reference:* [erdosproblems.com/217](https://www.erdosproblems.com/217)

For which `n` are there `n` points in `ℝ²`, no three on a line and no four on
a circle, which determine `n - 1` distinct distances and so that, in some
ordering of the distances, the `i`th distance occurs `i` times?

We use squared Euclidean distance. This is equivalent to using Euclidean
distance for comparing distances, since all squared distances are nonnegative.
-/

noncomputable section

namespace Erdos217

open Classical

/-- Points in the Euclidean plane, represented by coordinate pairs. -/
abbrev Point := ℝ × ℝ

/-- Squared Euclidean distance between two points in the plane. -/
def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/--
The signed twice-area determinant. Three points are collinear exactly when this
quantity is zero.
-/
def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) -
    (b.2 - a.2) * (c.1 - a.1)

/-- The unordered pairs of distinct indices, represented by the ordering `i < j`. -/
def indexPairs (n : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n × Fin n)).filter fun ij => ij.1 < ij.2

/-- The set of squared pairwise distances determined by an indexed point set. -/
def sqDistances {n : ℕ} (P : Fin n → Point) : Finset ℝ := by
  classical
  exact (indexPairs n).image fun ij => sqDist (P ij.1) (P ij.2)

/-- The number of unordered pairs of points at squared distance `d`. -/
def multiplicity {n : ℕ} (P : Fin n → Point) (d : ℝ) : ℕ := by
  classical
  exact ((indexPairs n).filter fun ij => sqDist (P ij.1) (P ij.2) = d).card

/-- No three indexed points are collinear. -/
def NoThreeCollinear {n : ℕ} (P : Fin n → Point) : Prop :=
  ∀ a b c : Fin n,
    a ≠ b → a ≠ c → b ≠ c →
      orient (P a) (P b) (P c) ≠ 0

/-- Four objects are pairwise distinct. -/
def PairwiseDistinct4 {α : Type _} (a b c d : α) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- Four indexed points lie on a common nondegenerate circle. -/
def Concyclic4 {n : ℕ} (P : Fin n → Point) (a b c d : Fin n) : Prop :=
  ∃ o : Point, ∃ r2 : ℝ,
    0 < r2 ∧
      sqDist (P a) o = r2 ∧
        sqDist (P b) o = r2 ∧
          sqDist (P c) o = r2 ∧
            sqDist (P d) o = r2

/-- No four indexed points are concyclic. -/
def NoFourConcyclic {n : ℕ} (P : Fin n → Point) : Prop :=
  ∀ a b c d : Fin n,
    PairwiseDistinct4 a b c d →
      ¬ Concyclic4 P a b c d

/--
`CrescentConfiguration n` says there are `n` injectively indexed points in
`ℝ²`, no three collinear and no four concyclic, determining exactly `n - 1`
distinct distances, with multiplicities `1, 2, ..., n - 1`.

The index `i : Fin (n - 1)` is zero-based, so the corresponding multiplicity is
`i.val + 1`.
-/
def CrescentConfiguration (n : ℕ) : Prop :=
  0 < n ∧
    ∃ P : Fin n → Point,
      Function.Injective P ∧
        NoThreeCollinear P ∧
          NoFourConcyclic P ∧
            (sqDistances P).card = n - 1 ∧
              ∃ order : Fin (n - 1) → ℝ,
                Function.Injective order ∧
                  (∀ d : ℝ, d ∈ sqDistances P ↔ ∃ i : Fin (n - 1), order i = d) ∧
                    ∀ i : Fin (n - 1),
                      multiplicity P (order i) = i.val + 1

/--
English version: For which `n` are there `n` points in `ℝ²`, no three on a line
and no four on a circle, determining `n - 1` distinct distances such that, in
some ordering, the `i`th distance occurs `i` times?
-/
@[category research open, AMS 5 52]
theorem erdos_217 : {n : ℕ | CrescentConfiguration n} = answer(sorry) := by
  sorry

end Erdos217

end

