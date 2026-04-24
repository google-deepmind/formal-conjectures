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
# Erdős Problem 1154

*References:*
- [erdosproblems.com/1154](https://www.erdosproblems.com/1154)
- [ErVo66] Erdős, Paul and Volkmann, Bodo, Additive Gruppen mit vorgegebener Hausdorffscher
  Dimension. J. Reine Angew. Math. (1966), 203--208.
- [EdMi01] Edgar, G. A. and Miller, Chris, Hausdorff dimension, analytic sets and transcendence.
  Real Anal. Exchange (2001/02), 335--339.
- [EdMi03] Edgar, G. A. and Miller, Chris, Borel subrings of the reals. Proc. Amer. Math. Soc.
  (2003), 1121--1129.
- [Ma16b] Mauldin, R. Daniel, Subfields of ℝ with arbitrary Hausdorff dimension. Math.
  Proc. Cambridge Philos. Soc. (2016), 157--165.

-/

open Set MeasureTheory Polynomial

namespace Erdos1154

/--
For every $a \in [0, 1]$, there exists a group in $\mathbb{R}$ with Hausdorff dimension $a$. This is
proved in [ErVo66].
-/
@[category research solved, AMS 12 16 28]
theorem erdos_1154.group {a : ℝ} (ha : a ∈ Icc 0 1) :
    ∃ R : AddSubgroup ℝ, dimH R.carrier = ENNReal.ofReal a := by
  sorry

/--
If a subring is analytic, then it is either equal to $\mathbb{R}$ or its Hausdorff dimension is
equal to $0$.
-/
@[category research solved, AMS 12 16 28]
theorem erdos_1154.analytic_ring {R : Subring ℝ} (hR : AnalyticSet R.carrier) :
    R = ⊤ ∨ dimH R.carrier = 0 := by
  sorry

/--
Does there exist, for every $a \in [0, 1]$, a ring in $\mathbb{R}$ with Hausdorff dimension $a$?
-/
@[category research open, AMS 12 16 28]
theorem erdos_1154.ring :
    answer(sorry) ↔
      ∀ a ∈ Set.Icc (0 : ℝ) 1, ∃ R : Subring ℝ, dimH R.carrier = ENNReal.ofReal a := by
  sorry

/-- A field `R` is real closed if
    1. `R` is real
    2. for all `x ∈ R`, either `x` or `-x` is a square
    3. every odd-degree polynomial has a root.
-/
class IsRealClosed (R : Type*) [Field R] : Prop extends IsSemireal R where
  isSquare_or_isSquare_neg (x : R) : IsSquare x ∨ IsSquare (-x)
  exists_isRoot_of_odd_natDegree {f : R[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x

/--
If a subfield is real closed and analytic, then it is either equal to $\mathbb{R}$ or its
Hausdorff dimension is equal to $0$.
-/
@[category research solved, AMS 12 16 28]
theorem erdos_1154.real_closed_analytic_field {R : Subfield ℝ} [IsRealClosed R]
    (hR : AnalyticSet R.carrier) :
    R = ⊤ ∨ dimH R.carrier = 0 := by
  sorry

/--
Does there exist, for every $a \in [0, 1]$, a field in $\mathbb{R}$ with Hausdorff dimension $a$?
-/
@[category research open, AMS 12 16 28]
theorem erdos_1154.field :
    answer(sorry) ↔
      ∀ a ∈ Set.Icc (0 : ℝ) 1, ∃ R : Subfield ℝ, dimH R.carrier = ENNReal.ofReal a := by
  sorry

end Erdos1154
