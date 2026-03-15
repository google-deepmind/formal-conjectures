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
# Erdős Problem 674

*Reference:* [erdosproblems.com/674](https://www.erdosproblems.com/674)

Are there any integer solutions to $x^x \cdot y^y = z^z$ with $x, y, z > 1$?

Ko [Ko40] proved there are none if $\gcd(x, y) = 1$, but there are in fact
infinitely many solutions in general — for example,
$x = 2^{12} \cdot 3^6$, $y = 2^8 \cdot 3^8$, $z = 2^{11} \cdot 3^7$.

In [Er79] Erdős asked if the infinite families found by Ko are the only
solutions.

[Ko40] Ko, C., _Note on the Diophantine equation $x^x y^y = z^z$_.
J. Chinese Math. Soc. (1940), 205–207.

[Er79] Erdős, P., _Some unconventional problems in number theory_.
Math. Mag. (1979), 67–70.

[Sc58] Schinzel, A., _Sur un problème de P. Erdős_. Colloq. Math. (1958), 198–204.

[Mi59] Mills, W. H., _An unsolved Diophantine equation_.
Rep. Inst. in the theory of numbers, University of Colorado (1959), 258–268.

[De75b] Dem'janenko, V. A., _On a conjecture of A. Schinzel_.
Izv. Vyssh. Ucheb. Zaved. Matematika (1975), 39–45.

[Uc84] Uchiyama, S., _On the Diophantine equation $x^x y^y = z^z$_.
Trudy Mat. Inst. Steklov. (1984), 237–243.
-/

namespace Erdos674

/--
Are there any natural numbers $x, y, z > 1$ such that $x^x \cdot y^y = z^z$? Yes — infinitely
many solutions exist, including the family found by Ko [Ko40].
-/
@[category research solved, AMS 11]
theorem erdos_674 : answer(True) ↔
    ∃ x y z : ℕ, x > 1 ∧ y > 1 ∧ z > 1 ∧ x ^ x * y ^ y = z ^ z := by
  sorry

/-- Are the infinite families found by Ko [Ko40] the only integer solutions
to $x^x \cdot y^y = z^z$ with $x, y, z > 1$? [Er79] -/
@[category research open, AMS 11]
theorem erdos_674.variants.unique_families : answer(sorry) ↔
    ∀ x y z : ℕ, x > 1 → y > 1 → z > 1 → x ^ x * y ^ y = z ^ z →
      sorry := by
  sorry

/-- Ko [Ko40] proved that there are no solutions to $x^x \cdot y^y = z^z$ with $x, y, z > 1$
when $\gcd(x, y) = 1$. -/
@[category research solved, AMS 11]
theorem erdos_674.variants.coprime_no_solution :
    ¬∃ x y z : ℕ, x > 1 ∧ y > 1 ∧ z > 1 ∧ Nat.Coprime x y ∧ x ^ x * y ^ y = z ^ z := by
  sorry

/-- The triple $(2^{12} \cdot 3^6,\; 2^8 \cdot 3^8,\; 2^{11} \cdot 3^7)$ is a solution
to $x^x \cdot y^y = z^z$. -/
@[category research solved, AMS 11]
theorem erdos_674.variants.witness :
    let x := 2 ^ 12 * 3 ^ 6
    let y := 2 ^ 8 * 3 ^ 8
    let z := 2 ^ 11 * 3 ^ 7
    x > 1 ∧ y > 1 ∧ z > 1 ∧ x ^ x * y ^ y = z ^ z := by
  sorry

end Erdos674
