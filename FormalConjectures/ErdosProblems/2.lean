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
Hough [Ho15] showed the answer is no; the best bounds are due to Balister, Bollobás,
Morris, Sahasrabudhe, and Tiba [BBMST22].

Related OEIS sequence: [A160559](https://oeis.org/A160559).

[Ho15] Hough, R. D., _Solution of the minimum modulus problem for covering systems_.
Ann. of Math. (2) **181** (2015), no. 1, 361–382.

[FFKPY07] Filaseta, M., Ford, K., Konyagin, S., Pomerance, C., and Yu, G., _Sieving by
large integers and covering systems of congruences_. J. Amer. Math. Soc. **20** (2007),
no. 2, 495–517.

[BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and Tiba, M.,
_On the Erdős covering problem: the density of the uncovered set_. Inventiones
mathematicae (2022), 377–414.

[Ow14] Owens, T., _A covering system with minimum modulus 42_. Thesis, Brigham Young
University (2014).
-/

namespace Erdos2

/--
Erdős asked whether the smallest modulus of a covering system can be arbitrarily
large (he expected the answer to be yes). Hough [Ho15], building on work of
Filaseta, Ford, Konyagin, Pomerance, and Yu [FFKPY07], showed the answer is **no**:
every covering system has smallest modulus at most $10^{16}$. Balister, Bollobás,
Morris, Sahasrabudhe, and Tiba [BBMST22] gave a simpler proof and improved the
bound to $616000$. The best known lower bound is $42$, due to Owens [Ow14].

Formally: there exists an absolute constant $B$ such that every covering system
of $\mathbb{Z}$ contains a congruence whose modulus is at most $B$.
-/
@[category research solved, AMS 11]
theorem erdos_2 :
    ∃ B : ℕ, ∀ c : CoveringSystem ℤ,
      ∃ i, ∃ m : ℕ, c.moduli i = Ideal.span {(m : ℤ)} ∧ m ≤ B := by
  sorry

/--
Balister, Bollobás, Morris, Sahasrabudhe, and Tiba [BBMST22] proved that every covering
system has a modulus at most $616000$. This is the best known explicit upper bound.
-/
@[category research solved, AMS 11]
theorem erdos_2_upper :
    ∀ c : CoveringSystem ℤ,
      ∃ i, ∃ m : ℕ, c.moduli i = Ideal.span {(m : ℤ)} ∧ m ≤ 616000 := by
  sorry

/--
Owens [Ow14] constructed a covering system whose minimum modulus is $42$. This is the
best known lower bound for the minimum modulus of a covering system.
-/
@[category research solved, AMS 11]
theorem erdos_2_lower :
    ∃ c : CoveringSystem ℤ,
      ∀ i, ∃ m : ℕ, c.moduli i = Ideal.span {(m : ℤ)} ∧ 42 ≤ m := by
  sorry

end Erdos2
