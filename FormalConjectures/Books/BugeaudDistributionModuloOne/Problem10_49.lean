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
# Bugeaud Collection of Conjectures and Open Questions: Normal in a Base and in Continued Fraction

Problem 10.49 asks for a real number that is normal to a given integer base and whose continued
fraction expansion is normal. It was extracted from Queffélec [Que06]. Scheerer [Sch17] and then
Becher and Yuhjtman [BY19] answered it, in the stronger form that asks for every base at once.

Normality to base $b$ is `NormalNumber.IsNormalInBase`: every block of $k$ digits occurs in the
base $b$ expansion with asymptotic frequency $b^{-k}$. Continued fraction normality is
`IsCFNormal`, stated as in [Sch17, (1.2)]: the orbit of $x$ under the Gauss map `gaussMap`
equidistributes with respect to the Gauss-Kuzmin measure `gaussKuzmin`. The last three
definitions are in `FormalConjecturesForMathlib`.

Both [Sch17] and [BY19] produce a *computable* number, and [BY19] computes the first $n$ partial
quotients in $O(n^4)$ operations. Computability and the operation count are not stated below.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Que06] Queffélec, Martine. "Old and new results on normality." Dynamics & Stochastics,
    IMS Lecture Notes Monograph Series 48 (2006): 225-236.
  - [Sch17](https://arxiv.org/abs/1701.07979) Scheerer, Adrian-Maria. "On the continued fraction
    expansion of absolutely normal numbers." arXiv preprint arXiv:1701.07979 (2017).
  - [BY19](https://arxiv.org/abs/1704.03622) Becher, Verónica, and Sergio A. Yuhjtman.
    "On absolutely normal and continued fraction normal numbers."
    International Mathematics Research Notices 2019.19 (2019): 6136-6161.
-/

namespace Bugeaud49

/--
Problem 10.49. For every integer base $b \ge 2$ there is a real number $\xi \in [0, 1)$ that is
normal to base $b$ and whose continued fraction expansion is normal. Posed in [Que06]; answered
by Scheerer [Sch17] and by Becher and Yuhjtman [BY19].

The base is prescribed, so the statement quantifies over $b$ first. The weaker reading, that
some base admits such a number, follows from this one.
-/
@[category research solved, AMS 11 37]
theorem problem_10_49 (b : ℕ) (hb : 2 ≤ b) :
    ∃ ξ ∈ Set.Ico (0 : ℝ) 1, NormalNumber.IsNormalInBase b ξ ∧ IsCFNormal ξ := by
  sorry

/--
What Scheerer [Sch17], Theorem 6.1, and Becher and Yuhjtman [BY19], Theorem 1, actually prove:
one real number $\xi \in [0, 1)$ is normal to *every* integer base $b \ge 2$ and continued
fraction normal at the same time. Both numbers are computable, and [BY19] computes the first $n$
partial quotients of theirs in $O(n^4)$ operations.
-/
@[category research solved, AMS 11 37]
theorem problem_10_49.variants.absolutely_normal :
    ∃ ξ ∈ Set.Ico (0 : ℝ) 1, NormalNumber.IsAbsolutelyNormal ξ ∧ IsCFNormal ξ := by
  sorry

/--
The metric backdrop of Problem 10.49, which is why the problem asks for a construction: by the
pointwise ergodic theorem, applied to the maps $x \mapsto bx \bmod 1$ and to the Gauss map,
almost every real number in $[0, 1)$ is absolutely normal and continued fraction normal
[Sch17, Section 1], [BY19].
-/
@[category research solved, AMS 11 37]
theorem problem_10_49.variants.almost_everywhere :
    ∀ᵐ ξ ∂(MeasureTheory.volume.restrict (Set.Ico (0 : ℝ) 1)),
      NormalNumber.IsAbsolutelyNormal ξ ∧ IsCFNormal ξ := by
  sorry

end Bugeaud49
