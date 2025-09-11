/-
Copyright 2025 Google LLC

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

--Wikipedia URL: https://en.wikipedia.org/wiki/Particular_values_of_the_Riemann_zeta_function
import FormalConjectures.Util.ProblemImports

namespace RiemannZeta

/--
$\zeta(5)$ is irrational.
-/
@[problem_status open]
theorem irrational_five : ∃ x, Irrational x ∧ riemannZeta 5 = x :=
  sorry

/--
$\zeta(7)$ is irrational.
-/
@[problem_status open]
theorem irrational_seven : ∃ x, Irrational x ∧ riemannZeta 7 = x :=
  sorry

/--
$\zeta(9)$ is irrational.
-/
@[problem_status open]
theorem irrational_nine : ∃ x, Irrational x ∧ riemannZeta 9 = x :=
  sorry

/--
$\zeta(11)$ is irrational.
-/
@[problem_status open]
theorem irrational_eleven : ∃ x, Irrational x ∧ riemannZeta 11 = x :=
  sorry

/--
$\zeta(2n + 1)$ is irrational for any $n\in\mathbb{N}$.
-/
@[problem_status open]
theorem irrational_odd (n : ℕ) : ∃ x, Irrational x ∧ riemannZeta (2 * n + 1) = x :=
  sorry

/--
$\zeta(3)$ is irrational.

[Ap79] Apéry, R. (1979). _Irrationalité de ζ(2) et ζ(3)_. Astérisque. 61: 11–13.
-/
@[problem_status solved]
theorem irrational_three : ∃ x, Irrational x ∧ riemannZeta 3 = x :=
  sorry

/--
There are infinite many $\zeta(2n + 1)$, $n \in \mathbb{N}$, that are irrational.

[Ri00] Rivoal, T. (2000). _La fonction zeta de Riemann prend une infinité de valeurs irrationnelles aux entiers impairs_. Comptes Rendus de l'Académie des Sciences, Série I. 331 (4): 267–270.
-/
@[problem_status solved]
theorem infinite_irrational_at_odd :
    { n | ∃ x, Irrational x ∧ riemannZeta (2 * n + 1) = x }.Infinite :=
  sorry

/--
At least one of $zeta(5), \zeta(7), \zeta(9)$ or $\zeta(11)$ is irrational.

[Zu01]  W. Zudilin (2001). _One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational_. Russ. Math. Surv. 56 (4): 774–776.
-/
@[problem_status solved]
theorem exists_irrational_of_five_seven_nine_eleven :
    {5, 7, 9, 11} ∩ { a | ∃ x, Irrational x ∧ riemannZeta a = x} |>.Nonempty :=
  sorry

end RiemannZeta
