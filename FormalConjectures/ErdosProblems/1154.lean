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
- [Ma16b] Mauldin, R. Daniel, Subfields of {\bf {R}} with arbitrary {H}ausdorff dimension. Math.
  Proc. Cambridge Philos. Soc. (2016), 157--165.

-/

namespace Erdos1154

/--
For every $a \in [0, 1]$, there exists a group in $\mathbb{R}$ with Hausdorff dimension $a$. This is
proved in [ErVo66].
-/
@[category research open, AMS 12 16 28]
theorem erdos_1154.group {a : ℝ} (ha : a ∈ Icc 0 1) :
    ∃ R : Subgroup ℝ, dimH (R : Set ℝ) = ENNReal.ofReal a := by
  sorry

/--
Does there exist, for every $a \in [0, 1]$, a ring in $\mathbb{R}$ with Hausdorff dimension $a$?
-/
@[category research open, AMS 12 16 28]
theorem erdos_1154.ring :
    answer(sorry) ↔
      ∀ a ∈ Set.Icc (0 : ℝ) 1, ∃ R : Subring ℝ, dimH (R : Set ℝ) = ENNReal.ofReal a := by
  sorry

/--
Does there exist, for every $a \in [0, 1]$, a ring in $\mathbb{R}$ with Hausdorff dimension $a$?
-/
@[category research open, AMS 12 16 28]
theorem erdos_1154.ring :
    answer(sorry) ↔
      ∀ a ∈ Set.Icc (0 : ℝ) 1, ∃ R : Subring ℝ, dimH (R : Set ℝ) = ENNReal.ofReal a := by
  sorry

/--
Does there exist, for every $a \in [0, 1]$, a field in $\mathbb{R}$ with Hausdorff dimension $a$?
-/
@[category research open, AMS 12 16 28]
theorem erdos_1154.ring :
    answer(sorry) ↔
      ∀ a ∈ Set.Icc (0 : ℝ) 1, ∃ R : Subfield ℝ, dimH (R : Set ℝ) = ENNReal.ofReal a := by
  sorry

end Erdos1154
