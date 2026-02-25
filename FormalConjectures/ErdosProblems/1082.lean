import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1082

*Reference:* [erdosproblems.com/1082](https://www.erdosproblems.com/1082)
-/

namespace Erdos1082

open EuclideanGeometry

/-- Given a finite set of points in the plane, we define the number of distinct distances between
pairs of points.

TODO(csonne): Remove this once formal conjectures is bumped.
-/
noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  (points.offDiag.image fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2).card

/-- The number of distinct distances from a finite set `points` to a point `pt`.

TODO(csonne): Move to ForMathlib.
-/
noncomputable def distinctDistancesFrom (points : Finset ℝ²) (pt : ℝ²) : ℕ :=
  (points.image fun x => dist x pt).card

/--
Let $A\subset \mathbb{R}^2$ be a set of $n$ points with no three on a line.
Does $A$ determine at least $\lfloor n/2\rfloor$ distinct distances?
-/
@[category research open, AMS 51]
theorem erdos_1082a : answer(sorry) ↔ ∀ (A : Finset ℝ²) (hA_n3c : NonTrilinear A.toSet),
    A.card / 2 ≤ distinctDistances A:= by
  sorry

/--
Let $A\subset \mathbb{R}^2$ be a set of $n$ points with no three on a line.
Must there exist a single point from which there are at least $\lfloor n/2\rfloor$ distinct
distances?

This question has been answered negatively by Xichuan in the
[comments](https://www.erdosproblems.com/forum/thread/1082), who gave a set of $42$ points in
$\mathbb{R}^2$, with no three on a line, such that each point determines only 20 distinct distances.
-/
@[category research solved, AMS 51]
theorem erdos_1082b : (∀ (A : Finset ℝ²) (hA : A.Nonempty) (hA_n3c : NonTrilinear A.toSet),
    ∃ (a : ℝ²) (ha : a ∈ A), A.card / 2 ≤ distinctDistancesFrom A a - 1) ↔ answer(False) := by
  sorry

end Erdos1082
