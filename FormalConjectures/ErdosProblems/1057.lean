/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1057

*References:*
- [erdosproblems.com/1057](https://www.erdosproblems.com/1057)
- [AGP94] Alford, W. R. and Granville, Andrew and Pomerance, Carl, There are infinitely many
  Carmichael numbers. Ann. of Math. (2) (1994), 703--722.
- [Er56c] Erdős, P., On pseudoprimes and Carmichael numbers. Publ. Math. Debrecen (1956),
  201--206.
- [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
- [Ha08] Harman, Glyn, Watt's mean value theorem and Carmichael numbers. Int. J. Number Theory
  (2008), 241--248.
- [Li22] J. D. Lichtman, Primes in arithmetic progressions to large moduli and shifted primes
  without large prime factors. arXiv:2211.09641 (2022).
- [Po89] Pomerance, Carl, Two methods in elementary analytic number theory. (1989), 135--161.
-/

open Nat Real Filter Set
open scoped Topology Asymptotics

namespace Erdos1057


/--
Let $C(x)$ count the number of Carmichael numbers in the interval $[1,x]$.
-/
noncomputable def C (x : ℝ) : ℝ :=
  ({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard : ℝ)

/--
Is it true that $C(x)=x^{1-o(1)}$?

This is discussed in problem A13 of Guy's collection [Gu04].
-/
@[category research open, AMS 11]
theorem erdos_1057 :
    answer(sorry) ↔ Tendsto (fun x ↦ Real.log (C x) / Real.log x) atTop (𝓝 1) := by
  sorry

/--
Erdős [Er56c] proved $C(x) < x \exp\left(-c \frac{\log x\log\log\log x}{\log\log x}\right)$
for some constant $c>0$.
-/
@[category research solved, AMS 11]
theorem erdos_1057.variants.upper_bound :
    ∃ c > 0, ∀ᶠ x in atTop,
      C x < x * Real.exp (-c * (Real.log x * Real.log (Real.log (Real.log x))) /
        Real.log (Real.log x)) := by
  sorry

/--
Pomerance [Po89] gave a heuristic suggesting that this is the true order of growth, and in fact
$C(x)= x \exp\left(-(1+o(1))\frac{\log x\log\log\log x}{\log\log x}\right)$.
-/
@[category research open, AMS 11]
theorem erdos_1057.variants.pomerance :
    answer(sorry) ↔ Tendsto (fun x ↦
      -(Real.log (C x / x) * Real.log (Real.log x)) /
      (Real.log x * Real.log (Real.log (Real.log x)))) atTop (𝓝 1) := by
  sorry

/--
Alford, Granville, and Pomerance [AGP94] proved that $C(x)\to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_1057.variants.agp_infinite :
    Tendsto C atTop atTop := by
  sorry

/--
Alford, Granville, and Pomerance [AGP94] proved that $C(x)>x^{2/7}$ for large $x$.
-/
@[category research solved, AMS 11]
theorem erdos_1057.variants.agp_lower_bound :
    ∀ᶠ x in atTop, C x > x ^ (2 / 7 : ℝ) := by
  sorry

/--
The lower bound $C(x)> x^{0.33336704}$ was proved by Harman [Ha08].
-/
@[category research solved, AMS 11]
theorem erdos_1057.variants.harman_lower_bound :
    ∀ᶠ x in atTop, C x > x ^ (0.33336704 : ℝ) := by
  sorry

/--
This exponent was improved to $0.3389$ by Lichtman [Li22].
-/
@[category research solved, AMS 11]
theorem erdos_1057.variants.lichtman_lower_bound :
    ∀ᶠ x in atTop, C x > x ^ (0.3389 : ℝ) := by
  sorry

end Erdos1057
