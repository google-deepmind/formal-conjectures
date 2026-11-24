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
module

public import FormalConjecturesUtil

/-!
# Sums of Four Integer Cubes

Unlike three-cube representations (see `FormalConjectures.Wikipedia.SumOfThreeCubes`), which omit
every integer congruent to $\pm 4 \pmod{9}$, the four-cube problem (Davenport 2008, pp. 173, 177)
conjectures that every integer $n \in \mathbb{Z}$ equals $x^3 + y^3 + z^3 + w^3$ for some
$x, y, z, w \in \mathbb{Z}$. Work by Sierpiński (with Schinzel, 1958) and Demjanenko (1966) settles
all residue classes modulo $9$ except $9k \pm 4$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Sum_of_four_cubes_problem)
- W. Sierpiński and A. Schinzel, *Sur les sommes de quatre cubes*, Acta Arithmetica **4** (1958),
  20–30.
- V. A. Demjanenko, *On sums of four cubes*, Izvestiya Vysshikh Uchebnykh Zavedenii. Matematika
  **1966** (1966), no. 5 (54), 63–69.
- H. Cohen, *Sums of four cubes*, 2004.
- H. Davenport, *The Higher Arithmetic: An Introduction to the Theory of Numbers*, 8th ed.,
  Cambridge University Press, 2008, pp. 173, 177.
-/

@[expose] public section

namespace SumOfFourCubes

/-- The predicate that `n : R` is a sum of four cubes in `R`. -/
def IsSumOfFourCubes {R : Type*} [Ring R] (n : R) : Prop :=
  ∃ x y z w : R, n = x ^ 3 + y ^ 3 + z ^ 3 + w ^ 3

/-- Sums of four cubes in a commutative ring are closed under negation. -/
@[category API, AMS 11]
theorem isSumOfFourCubes_neg_iff {R : Type*} [CommRing R] (n : R) :
    IsSumOfFourCubes (-n) ↔ IsSumOfFourCubes n := by
  constructor
  · rintro ⟨x, y, z, w, h⟩
    refine ⟨-x, -y, -z, -w, ?_⟩
    linear_combination -h
  · rintro ⟨x, y, z, w, h⟩
    refine ⟨-x, -y, -z, -w, ?_⟩
    linear_combination -h

/-- Every integer multiple of $6$ is a sum of four integer cubes via
$6k = (k + 1)^3 + (k - 1)^3 + (-k)^3 + (-k)^3$ (see Sierpiński–Schinzel 1958 and Cohen 2004). -/
@[category textbook, AMS 11]
theorem isSumOfFourCubes_six_mul (k : ℤ) :
    IsSumOfFourCubes (6 * k) :=
  ⟨k + 1, k - 1, -k, -k, by ring⟩

/-- Every odd multiple of $3$ is a sum of four integer cubes via Cohen's (2004) identity
$6k + 3 = k^3 + (-k + 4)^3 + (2k - 5)^3 + (-2k + 4)^3$. -/
@[category textbook, AMS 11]
theorem isSumOfFourCubes_six_mul_add_three (k : ℤ) :
    IsSumOfFourCubes (6 * k + 3) :=
  ⟨k, -k + 4, 2 * k - 5, -2 * k + 4, by ring⟩

/-- $4 = 10^3 + 7^3 + (-2)^3 + (-11)^3$ is a sum of four integer cubes. -/
@[category test, AMS 11]
theorem isSumOfFourCubes_four : IsSumOfFourCubes (4 : ℤ) :=
  ⟨10, 7, -2, -11, by norm_num⟩

/-- $5 = 2^3 + (-1)^3 + (-1)^3 + (-1)^3$ is a sum of four integer cubes. -/
@[category test, AMS 11]
theorem isSumOfFourCubes_five : IsSumOfFourCubes (5 : ℤ) :=
  ⟨2, -1, -1, -1, by norm_num⟩

/-- $13 = 16^3 + (-14)^3 + (-11)^3 + (-2)^3$ is a sum of four integer cubes. -/
@[category test, AMS 11]
theorem isSumOfFourCubes_thirteen : IsSumOfFourCubes (13 : ℤ) :=
  ⟨16, -14, -11, -2, by norm_num⟩

/--
**Four-cubes conjecture**: every integer $n \in \mathbb{Z}$ admits a representation
$n = x^3 + y^3 + z^3 + w^3$ with $x, y, z, w \in \mathbb{Z}$.
-/
@[category research open, AMS 11]
theorem sum_of_four_cubes (n : ℤ) : IsSumOfFourCubes n := by
  sorry

/--
Each integer $9k + 4$ ($k \in \mathbb{Z}$) is a sum of four integer cubes. By
`sierpinski_schinzel_demjanenko` and `isSumOfFourCubes_neg_iff` (since
$-(9k + 4) = 9(-k - 1) + 5$), this single residue class is equivalent to `sum_of_four_cubes`.
-/
@[category research open, AMS 11]
theorem sum_of_four_cubes.variants.nine_mul_add_four (k : ℤ) :
    IsSumOfFourCubes (9 * k + 4) := by
  sorry

/--
Sierpiński and Schinzel (1958) and Demjanenko (1966) proved that every integer $n$ satisfying
$n \not\equiv 4, 5 \pmod{9}$ is a sum of four integer cubes.
-/
@[category research solved, AMS 11]
theorem sierpinski_schinzel_demjanenko (n : ℤ) (h : ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])) :
    IsSumOfFourCubes n := by
  sorry

end SumOfFourCubes
