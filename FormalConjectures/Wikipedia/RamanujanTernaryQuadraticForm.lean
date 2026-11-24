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
# Ramanujan's Ternary Quadratic Form $x^2 + y^2 + 10 z^2$

In 1916, Srinivasa Ramanujan [Ra16] observed, and Leonard Dickson [Di27] proved, that whereas the
even natural numbers missed over $\mathbb{Z}$ by $x^2 + y^2 + 10 z^2$ are precisely
$4^a (16 b + 6)$ ($a, b \ge 0$), the missed odd integers behave sporadically. Following extensions
of Ramanujan's list by Jones and Pall ($679$), Gupta ($2719$), and Galway (up to
$2 \times 10^{10}$), Ken Ono and Kannan Soundararajan [OS97] conjectured that the $18$ odd values
up to $2719$ exhaust all odd exceptions and proved this under the Generalized Riemann Hypothesis.
Earlier, Duke and Schulze-Pillot [DSP90] established unconditionally that the set of odd exceptions
is finite. Giving an unconditional proof of the Ono–Soundararajan list remains open.

*References:*
- [Wikipedia: Ramanujan's form](https://en.wikipedia.org/wiki/Ramanujan%27s_ternary_quadratic_form)
- [Ra16] S. Ramanujan, *On the expression of a number in the form $ax^2 + by^2 + cz^2 + du^2$*,
  Proc. Cambridge Philos. Soc. **19** (1916), 11–21.
- [Di27] L. E. Dickson, *Ternary quadratic forms and congruences*, Ann. of Math. (2) **28**
  (1926–1927), 333–341. https://doi.org/10.2307/1968378
- [DSP90] W. Duke and R. Schulze-Pillot, *Representation of integers by positive ternary quadratic
  forms and equidistribution of lattice points on ellipsoids*, Invent. Math. **99** (1990), 49–57.
  https://doi.org/10.1007/BF01234411
- [OS97] K. Ono and K. Soundararajan, *Ramanujan's ternary quadratic form*, Invent. Math. **130**
  (1997), no. 3, 415–454. https://doi.org/10.1007/s002220050191
-/

@[expose] public section

namespace RamanujanTernaryQuadraticForm

/-- A natural number $n$ is represented over $\mathbb{Z}$ by $x^2 + y^2 + 10 z^2$. -/
def IsRamanujanTernaryRep (n : ℕ) : Prop :=
  ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 10 * z ^ 2 = (n : ℤ)

/-- The $18$ known odd positive integers not represented by $x^2 + y^2 + 10 z^2$. -/
def ramanujanOddExceptions : Finset ℕ :=
  {3, 7, 21, 31, 33, 43, 67, 79, 87, 133, 217, 219, 223, 253, 307, 391, 679, 2719}

/-- `ramanujanOddExceptions` consists of $18$ distinct integers. -/
@[category test, AMS 11]
theorem card_ramanujanOddExceptions : ramanujanOddExceptions.card = 18 := by
  decide

/-- Every element of `ramanujanOddExceptions` is odd. -/
@[category test, AMS 11]
theorem odd_of_mem_ramanujanOddExceptions : ∀ m ∈ ramanujanOddExceptions, Odd m := by
  decide

/-- $11 = 1^2 + 0^2 + 10 \cdot 1^2$ is represented over $\mathbb{Z}$ by $x^2 + y^2 + 10 z^2$. -/
@[category test, AMS 11]
theorem isRamanujanTernaryRep_eleven : IsRamanujanTernaryRep 11 :=
  ⟨1, 0, 1, by norm_num⟩

/-- Over $\mathbb{Z}$, $x^2 + y^2 + 10 z^2 = n$ is equivalent to a bounded natural-number search
over $z \le \lfloor \sqrt{n / 10} \rfloor$ and $x \le \lfloor \sqrt{n} \rfloor$. -/
@[category API, AMS 11]
theorem isRamanujanTernaryRep_iff_bounded (n : ℕ) :
    IsRamanujanTernaryRep n ↔
      ∃ z ∈ Finset.range ((n / 10).sqrt + 1), ∃ x ∈ Finset.range (n.sqrt + 1),
        x ^ 2 + 10 * z ^ 2 + Nat.sqrt (n - (x ^ 2 + 10 * z ^ 2)) ^ 2 = n := by
  constructor
  · rintro ⟨x₀, y₀, z₀, hxyz⟩
    have hnat : x₀.natAbs ^ 2 + y₀.natAbs ^ 2 + 10 * z₀.natAbs ^ 2 = n := by
      have hsq : (x₀.natAbs : ℤ) ^ 2 + (y₀.natAbs : ℤ) ^ 2 + 10 * (z₀.natAbs : ℤ) ^ 2 = n := by
        simpa [Int.natAbs_sq] using hxyz
      exact_mod_cast hsq
    have hz : z₀.natAbs ≤ (n / 10).sqrt := Nat.le_sqrt.mpr (by rw [← sq]; omega)
    have hx : x₀.natAbs ≤ n.sqrt := Nat.le_sqrt.mpr (by rw [← sq]; omega)
    refine ⟨z₀.natAbs, Finset.mem_range.mpr (by omega),
      x₀.natAbs, Finset.mem_range.mpr (by omega), ?_⟩
    have hr : n - (x₀.natAbs ^ 2 + 10 * z₀.natAbs ^ 2) = y₀.natAbs * y₀.natAbs := by
      rw [← sq]; omega
    rw [hr, Nat.sqrt_eq]
    omega
  · rintro ⟨z, _, x, _, h⟩
    refine ⟨x, Nat.sqrt (n - (x ^ 2 + 10 * z ^ 2)), z, ?_⟩
    have h' : x ^ 2 + Nat.sqrt (n - (x ^ 2 + 10 * z ^ 2)) ^ 2 + 10 * z ^ 2 = n := by omega
    exact_mod_cast h'

/-- Bounded-search decidability for `IsRamanujanTernaryRep`. -/
instance decidablePredIsRamanujanTernaryRep : DecidablePred IsRamanujanTernaryRep :=
  fun n ↦ decidable_of_iff
    (∃ z ∈ Finset.range ((n / 10).sqrt + 1), ∃ x ∈ Finset.range (n.sqrt + 1),
      x ^ 2 + 10 * z ^ 2 + Nat.sqrt (n - (x ^ 2 + 10 * z ^ 2)) ^ 2 = n)
    (isRamanujanTernaryRep_iff_bounded n).symm

/-- None of the $18$ integers in `ramanujanOddExceptions` is represented over $\mathbb{Z}$ by
$x^2 + y^2 + 10 z^2$. -/
@[category test, AMS 11]
theorem not_isRamanujanTernaryRep_of_mem_ramanujanOddExceptions :
    ∀ m ∈ ramanujanOddExceptions, ¬ IsRamanujanTernaryRep m := by
  decide +kernel

/-- $6 = 4^0 (16 \cdot 0 + 6)$ is the smallest even integer missed over $\mathbb{Z}$ by
$x^2 + y^2 + 10 z^2$. -/
@[category test, AMS 11]
theorem not_isRamanujanTernaryRep_six : ¬ IsRamanujanTernaryRep 6 := by
  decide +kernel

/-- Every square $a^2$ is represented by $x^2 + y^2 + 10 z^2$. -/
@[category API, AMS 11]
theorem isRamanujanTernaryRep_sq (a : ℕ) : IsRamanujanTernaryRep (a ^ 2) :=
  ⟨a, 0, 0, by push_cast; ring⟩

/-- `IsRamanujanTernaryRep` is closed under multiplication by squares. -/
@[category API, AMS 11]
theorem isRamanujanTernaryRep_mul_sq {n : ℕ} (a : ℕ) (h : IsRamanujanTernaryRep n) :
    IsRamanujanTernaryRep (a ^ 2 * n) := by
  rcases h with ⟨x, y, z, hxyz⟩
  refine ⟨a * x, a * y, a * z, ?_⟩
  push_cast
  linear_combination (a : ℤ) ^ 2 * hxyz

/--
**Ramanujan–Dickson Characterization of Even Exceptions** [Ra16, Di27]: An even natural number $n$
fails to be represented over $\mathbb{Z}$ by $x^2 + y^2 + 10 z^2$ if and only if
$n = 4^a (16 b + 6)$ for some $a, b \in \mathbb{N}$.
-/
@[category research solved, AMS 11]
theorem ramanujan_ternary_even_exceptions {n : ℕ} (heven : Even n) :
    ¬ IsRamanujanTernaryRep n ↔ ∃ a b : ℕ, n = 4 ^ a * (16 * b + 6) := by
  sorry

/--
**Duke–Schulze-Pillot Finiteness Theorem** [DSP90]: Only finitely many odd natural numbers fail to
be represented over $\mathbb{Z}$ by $x^2 + y^2 + 10 z^2$.
-/
@[category research solved, AMS 11]
theorem ramanujan_ternary_odd_exceptions_finite :
    {n : ℕ | Odd n ∧ ¬ IsRamanujanTernaryRep n}.Finite := by
  sorry

/--
**Ono–Soundararajan Conjecture** [OS97]: Unconditionally, the odd natural numbers not represented
over $\mathbb{Z}$ by $x^2 + y^2 + 10 z^2$ are precisely the $18$ elements of
`ramanujanOddExceptions`. Ono and Soundararajan [OS97] proved this conditionally under the
Generalized Riemann Hypothesis.
-/
@[category research open, AMS 11]
theorem ono_soundararajan_conjecture :
    {n : ℕ | Odd n ∧ ¬ IsRamanujanTernaryRep n} = (ramanujanOddExceptions : Set ℕ) := by
  sorry

end RamanujanTernaryQuadraticForm
