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
# Erdős Problem 214

*References:*
- [erdosproblems.com/214](https://www.erdosproblems.com/214)
- [CsTo94] Csizmadia, György and Tóth, Géza, *Note on a Ramsey-type problem in geometry*.
  J. Combin. Theory Ser. A (1994), 302-306.
- [EGMRSS75] Erdős, P. and Graham, R. L. and Montgomery, P. and Rothschild, B. L. and Spencer, J.
  and Straus, E. G., *Euclidean Ramsey theorems. II*. (1975), 529-557.
- [Ju79] Juhász, Rozália, *Ramsey type theorems in the plane*. J. Combin. Theory Ser. A (1979),
  152-160.
-/

open scoped Congruent EuclideanGeometry

namespace Erdos214

/-- The four vertices of a unit square. -/
def unitSquare : Fin 4 → ℝ² := ![!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]]

/-- Colouring the points of `S` blue and the points of `Sᶜ` red gives a red/blue colouring of
$\mathbb{R}^2$; it is unit-distance-avoiding if no two blue points are distance $1$ apart. -/
def UnitDistanceAvoiding (S : Set ℝ²) : Prop := ∀ x ∈ S, ∀ y ∈ S, dist x y ≠ 1

/-- Any unit-distance-avoiding colouring contains a congruent red copy of every set of `n`
points. -/
def HasRedCopies (n : ℕ) : Prop :=
  ∀ S : Set ℝ², UnitDistanceAvoiding S → ∀ K : Fin n → ℝ², Function.Injective K →
    ∃ p : Fin n → ℝ², (∀ i, p i ∈ Sᶜ) ∧ (p ≅ K)

/-- The largest integer `k` such that any unit-distance-avoiding colouring contains a congruent
red copy of every set of `k` points. -/
noncomputable def k : ℕ := sSup {n | HasRedCopies n}

/--
Let $S\subset \mathbb{R}^2$ be such that no two points in $S$ are distance $1$ apart. Must the
complement of $S$ contain four points which form a unit square?

The answer is yes, proved by Juhász [Ju79], who proved more generally that the complement of $S$
must contain a congruent copy of any set of four points.
-/
@[category research solved, AMS 5 52]
theorem erdos_214 : answer(True) ↔
    ∀ S : Set ℝ², UnitDistanceAvoiding S →
      ∃ p : Fin 4 → ℝ², (∀ i, p i ∈ Sᶜ) ∧ (p ≅ unitSquare) := by
  sorry

/--
The answer is yes, proved by Juhász [Ju79], who proved more generally that the complement of $S$
must contain a congruent copy of any set of four points.
-/
@[category research solved, AMS 5 52]
theorem erdos_214.variants.juhasz : HasRedCopies 4 := by
  sorry

/--
Erdős, Graham, Montgomery, Rothschild, Spencer, and Straus [EGMRSS75] had earlier showed that
$3\leq k\leq 10^{12}$.
-/
@[category research solved, AMS 5 52]
theorem erdos_214.variants.egmrss : 3 ≤ k ∧ k ≤ 10 ^ 12 := by
  sorry

/--
Juhász [Ju79] also improved the upper bound to $k\leq 11$.
-/
@[category research solved, AMS 5 52]
theorem erdos_214.variants.juhasz_twelve_points : ¬ HasRedCopies 12 := by
  sorry

/--
The upper bound was improved further by Csizmadia and Tóth [CsTo94] to $k\leq 7$.
-/
@[category research solved, AMS 5 52]
theorem erdos_214.variants.csizmadia_toth : ¬ HasRedCopies 8 := by
  sorry

/--
The best known bounds currently are
\[4\leq k\leq 7.\]
-/
@[category research solved, AMS 5 52]
theorem erdos_214.variants.bounds : 4 ≤ k ∧ k ≤ 7 := by
  sorry

end Erdos214
