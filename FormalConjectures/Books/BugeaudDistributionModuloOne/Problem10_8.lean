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
import FormalConjecturesForMathlib.Data.Real.NearestInt
/-!
# Bugeaud Collection of Conjectures and Open Questions: $p$-adic Littlewood Conjecture

This is the $p$-adic analogue of the Littlewood conjecture, posed by de Mathan and
Teulié. A liminf-based formulation also appears in the file
`FormalConjectures/Wikipedia/LittlewoodConjecture.lean` as `padic_littlewood_conjecture`.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [dMT04] de Mathan, Bernard, and Olivier Teulié. "Problèmes diophantiens simultanés."
    Monatshefte für Mathematik 143.3 (2004): 229-245.
  - [EK07] Einsiedler, Manfred, and Dmitry Kleinbock. "Measure rigidity and $p$-adic
    Littlewood-type problems." Compositio Mathematica 143.3 (2007): 689-702.
-/

namespace Bugeaud08

/--
Problem 10.8 ($p$-adic Littlewood conjecture). For every real number $\xi$ and
every prime number $p$,
$$\inf_{q \ge 1} q \cdot \lVert q \xi \rVert \cdot |q|_p = 0,$$
where $\lVert \cdot \rVert$ denotes the distance to the nearest integer and
$|\cdot|_p$ denotes the $p$-adic absolute value. Posed by de Mathan and
Teulié [dMT04].
-/
@[category research open, AMS 11]
theorem problem_10_8 (ξ : ℝ) (p : ℕ) (hp : p.Prime) :
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0 := by
  sorry

/--
The quadratic case of Problem 10.8. de Mathan and Teulié [dMT04] solved the
$p$-adic Littlewood conjecture for quadratic real numbers.
-/
@[category research solved, AMS 11]
theorem problem_10_8.variants.quadratic (ξ : ℝ) (p : ℕ) (hp : p.Prime)
    (hξ : (minpoly ℚ ξ).natDegree = 2) :
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0 := by
  sorry

/--
The exceptional set for Problem 10.8 has Hausdorff dimension zero (Einsiedler
and Kleinbock [EK07].
-/
@[category research solved, AMS 11]
theorem problem_10_8.variants.exceptional_set_dimH_zero (p : ℕ) (hp : p.Prime) :
    dimH {ξ : ℝ | Filter.atTop.liminf
      (fun q : ℕ ↦ q * padicNorm p q * distToNearestInt (q * ξ)) ≠ 0} = 0 := by
  sorry

end Bugeaud08
