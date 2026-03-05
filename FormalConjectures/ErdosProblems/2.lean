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
# Erdős Problem 2

*Reference:* [erdosproblems.com/2](https://www.erdosproblems.com/2)

Erdős asked whether the smallest modulus of a covering system can be arbitrarily large.
Hough [Hou15] showed the answer is no; the best bounds are due to Balister, Bollobás,
Morris, Sahasrabudhe, and Tiba [BBMST22].

[Hou15] Hough, R. D., _Solution of the minimum modulus problem for covering systems_.
Annals of Mathematics (2015), 361-382.

[FFKPY07] Filaseta, M., Ford, K., Konyagin, S., Pomerance, C., and Yu, G., _Sieving by
large integers and covering systems of congruences_. Journal of the American Mathematical
Society (2007), 495-517.

[BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and Tiba, M.,
_The Erdős covering conjecture_. Annals of Mathematics (2022).

[Ow14] Owens, T., _A covering system with minimum modulus 42_. (2014).
-/

namespace Erdos2

/--
A finite system of congruences $\{(a_i, m_i)\}$ is a **covering system** if every
modulus is positive and every integer satisfies at least one congruence $n \equiv a_i \pmod{m_i}$.
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, 0 < p.2) ∧
  (∀ n : ℤ, ∃ p ∈ S, (p.2 : ℤ) ∣ (n - p.1))

/--
Erdős asked whether the smallest modulus of a covering system can be arbitrarily
large (he expected the answer to be yes). Hough [Hou15], building on work of
Filaseta, Ford, Konyagin, Pomerance, and Yu [FFKPY07], showed the answer is **no**:
every covering system has smallest modulus at most $10^{16}$. Balister, Bollobás,
Morris, Sahasrabudhe, and Tiba [BBMST22] gave a simpler proof and improved the
bound to $616000$. The best known lower bound is $42$, due to Owens [Ow14].

Formally: there exists an absolute constant $B$ such that every covering system
contains a congruence whose modulus is at most $B$.
-/
@[category research solved, AMS 11]
theorem erdos_2 :
    ∃ B : ℕ, ∀ S : Finset (ℤ × ℕ), IsCoveringSystem S →
      ∃ p ∈ S, p.2 ≤ B := by
  sorry

end Erdos2
