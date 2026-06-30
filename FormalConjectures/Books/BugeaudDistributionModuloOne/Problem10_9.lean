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
import FormalConjectures.Wikipedia.Mahler32
/-!
# Bugeaud Collection of Conjectures and Open Questions: Mahler's Z-numbers

See also FormalConjectures/Wikipedia/Mahler32.lean.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Mah68] Mahler, Kurt. "An unsolved problem on the powers of 3/2."
    Journal of the Australian Mathematical Society 8.2 (1968): 313-321.
  - [FLP95] Flatto, Leopold, Jeffrey C. Lagarias, and Andrew D. Pollington.
    "On the range of fractional parts $\{\xi(p/q)^n\}$."
    Acta Arithmetica 70.2 (1995): 125-147.
-/

namespace Bugeaud09

/--
Problem 10.9. There are no real numbers $\xi$ such that
$0 \le \{\xi (3/2)^n\} < 1/2$ for every positive integer $n$,
i.e. no Z-number exists. Posed by Mahler [Mah68].
-/
@[category research open, AMS 11]
theorem problem_10_9 : type_of% Mahler32.mahler_conjecture := by
  sorry

/--
Sanity check: `1` is not a Z-number, since for `n = 1` we have
$\{1 \cdot (3/2)^1\} = \{3/2\} = 1/2 \not< 1/2$.
-/
@[category test, AMS 11]
theorem not_isZNumber_one : ¬ IsZNumber 1 := by
  rintro ⟨-, h⟩
  have h1 := h 1 le_rfl
  rw [pow_one, one_mul] at h1
  have hfr : Int.fract (3 / 2 : ℝ) = 1 / 2 := by rw [Int.fract]; norm_num [Int.floor_eq_iff]
  rw [hfr] at h1
  exact lt_irrefl _ h1

/--
Mahler [Mah68] proved that the set of Z-numbers has Lebesgue measure zero.
-/
@[category research solved, AMS 11]
theorem problem_10_9.variants.measure_zero :
    MeasureTheory.volume {ξ : ℝ | IsZNumber ξ} = 0 := by
  sorry

/--
Flatto, Lagarias, and Pollington [FLP95] proved that the set of Z-numbers has
Hausdorff dimension strictly less than $1$.
-/
@[category research solved, AMS 11]
theorem problem_10_9.variants.dimH_lt_one :
    dimH {ξ : ℝ | IsZNumber ξ} < 1 := by
  sorry

end Bugeaud09
