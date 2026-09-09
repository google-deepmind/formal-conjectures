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
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-!
# The discriminant of a cubic

* `Cubic.rootMultiplicity_le_one_of_discr_ne_zero`: a cubic with nonzero discriminant has only
  simple roots.
* `Cubic.discr_nonneg_of_splits`: over a linearly ordered field, a cubic that splits has
  nonnegative discriminant. Contrapositively, a cubic of negative discriminant does not split, so
  over $\mathbb{R}$ it has exactly one real root.
-/

namespace Cubic

variable {K : Type*} [Field K] {P : Cubic K}

theorem rootMultiplicity_le_one_of_discr_ne_zero (ha : P.a ≠ 0) (hd : P.discr ≠ 0) (x : K) :
    Polynomial.rootMultiplicity x P.toPoly ≤ 1 := by
  refine Polynomial.rootMultiplicity_le_one_of_separable ?_ x
  simpa [← Polynomial.nodup_aroots_iff_of_splits (K := AlgebraicClosure K) (ne_zero_of_a_ne_zero ha)
    (IsAlgClosed.splits _), Polynomial.aroots_def, ← map_roots] using
    (discr_ne_zero_iff_roots_nodup ha (IsAlgClosed.splits _)).mp hd

theorem discr_nonneg_of_splits [LinearOrder K] [IsStrictOrderedRing K]
    {P : Cubic K} (ha : P.a ≠ 0) (hP : (P.toPoly.map (RingHom.id K)).Splits) : 0 ≤ P.discr := by
  obtain ⟨x, y, z, h3⟩ := (splits_iff_roots_eq_three ha).mp hP
  simpa using (discr_eq_prod_three_roots ha h3).ge.trans' (sq_nonneg _)

end Cubic
