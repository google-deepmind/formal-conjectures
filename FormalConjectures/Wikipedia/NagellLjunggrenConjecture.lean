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
# The Nagell–Ljunggren Conjecture on Perfect-Power Repunits

Trygve Nagell (1920) and Wilhelm Ljunggren (1943) studied the exponential Diophantine equation
$$\frac{x^n - 1}{x - 1} = y^q \qquad (x > 1,\; y > 1,\; n > 2,\; q \ge 2),$$
asking which repunits `Nat.repunit x n` of length $n \ge 3$ in base $x$ are nontrivial perfect
powers (compare `FormalConjectures.Wikipedia.Goormaghtigh` and
`FormalConjectures.Wikipedia.RepunitPrime`). For $q = 2$, Nagell (1920) solved $n = 4$ and
Ljunggren (1943) settled all $n > 2$, isolating $(x, y, n, q) = (3, 11, 5, 2)$
($11^2 = 121 = 11111_3$) and $(7, 20, 4, 2)$ ($20^2 = 400 = 1111_7$). Bugeaud and Mignotte (2002)
conjectured that across all $q \ge 2$ the sole further solution is $(18, 7, 3, 3)$
($7^3 = 343 = 111_{18}$), so the perfect powers representable as repunits of length at least $3$
equal $\{121, 343, 400\}$ (OEIS A208242).

*References:*
- [Wikipedia: Repdigit](https://en.wikipedia.org/wiki/Repdigit)
- [OEIS A208242](https://oeis.org/A208242)
- T. Nagell, *Note sur l'équation indéterminée $(x^n - 1)/(x - 1) = y^q$*, Norsk Mat. Tidsskr.
  **2** (1920), 75–78.
- W. Ljunggren, *Noen setninger om ubestemte likninger av formen $(x^n - 1)/(x - 1) = y^q$*,
  Norsk Mat. Tidsskr. **25** (1943), 17–20.
- Y. Bugeaud and M. Mignotte, *L'équation de Nagell–Ljunggren $(x^n - 1)/(x - 1) = y^q$*,
  Enseign. Math. **48** (2002), 147–168.
-/

@[expose] public section

namespace NagellLjunggrenConjecture

/-- Parameters $(x, y, n, q)$ solving $\sum_{k=0}^{n-1} x^k = y^q$ (`Nat.repunit`) in integers
$1 < x$, $1 < y$, $2 < n$, and $2 \le q$. -/
def IsNagellLjunggrenSolution (x y n q : ℕ) : Prop :=
  1 < x ∧ 1 < y ∧ 2 < n ∧ 2 ≤ q ∧ Nat.repunit x n = y ^ q

instance instDecidableIsNagellLjunggrenSolution (x y n q : ℕ) :
    Decidable (IsNagellLjunggrenSolution x y n q) := by
  unfold IsNagellLjunggrenSolution Nat.repunit
  infer_instance

/-- Cubic witness $(18, 7, 3, 3)$: $1 + 18 + 18^2 = 343 = 7^3$. -/
@[category test, AMS 11]
theorem isNagellLjunggrenSolution_18_7_3_3 :
    IsNagellLjunggrenSolution 18 7 3 3 := by
  decide

/-- Base-$3$ square witness $(3, 11, 5, 2)$: $1 + 3 + 9 + 27 + 81 = 121 = 11^2$. -/
@[category test, AMS 11]
theorem isNagellLjunggrenSolution_3_11_5_2 :
    IsNagellLjunggrenSolution 3 11 5 2 := by
  decide

/-- Base-$7$ square witness $(7, 20, 4, 2)$: $1 + 7 + 49 + 343 = 400 = 20^2$. -/
@[category test, AMS 11]
theorem isNagellLjunggrenSolution_7_20_4_2 :
    IsNagellLjunggrenSolution 7 20 4 2 := by
  decide

/-- Non-solution sanity check: $(2, 3, 3, 2)$ fails because $1 + 2 + 4 = 7 \ne 3^2$. -/
@[category test, AMS 11]
theorem not_isNagellLjunggrenSolution_2_3_3_2 :
    ¬ IsNagellLjunggrenSolution 2 3 3 2 := by
  decide

/-- Multiplicative form of the Nagell–Ljunggren equation: $(x, y, n, q)$ satisfies
`IsNagellLjunggrenSolution` if and only if $1 < x$, $1 < y$, $2 < n$, $2 \le q$, and
$x^n - 1 = (x - 1) y^q$. -/
@[category API, AMS 11]
theorem isNagellLjunggrenSolution_iff_pow_sub_one (x y n q : ℕ) :
    IsNagellLjunggrenSolution x y n q ↔
      1 < x ∧ 1 < y ∧ 2 < n ∧ 2 ≤ q ∧ x ^ n - 1 = (x - 1) * y ^ q := by
  unfold IsNagellLjunggrenSolution
  refine and_congr_right fun hx => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [← Nat.mul_repunit_eq_pow_sub_one x n]
  exact (Nat.mul_right_inj (by omega : x - 1 ≠ 0)).symm

/-- Exhaustive check of the $q = 2$ case on $2 \le x \le 4$, $2 \le y \le 12$, and $3 \le n \le 5$,
confirming $(3, 11, 5)$ is the sole solution in this box. -/
@[category test, AMS 11]
theorem nagellLjunggren_small_square_box :
    ∀ x ∈ Finset.Icc 2 4, ∀ y ∈ Finset.Icc 2 12, ∀ n ∈ Finset.Icc 3 5,
      IsNagellLjunggrenSolution x y n 2 ↔ (x, y, n) = (3, 11, 5) := by
  decide

/--
**Nagell–Ljunggren Square-Repunit Theorem** (Nagell 1920 for $n = 4$; Ljunggren 1943 for all
$n > 2$): the equation $\sum_{k=0}^{n-1} x^k = y^2$ in integers $x > 1$, $y > 1$, and $n > 2$
admits only $(3, 11, 5, 2)$ and $(7, 20, 4, 2)$.
-/
@[category research solved, AMS 11]
theorem nagell_ljunggren_square_repunit_theorem :
    {(x, y, n, q) : ℕ × ℕ × ℕ × ℕ | IsNagellLjunggrenSolution x y n q ∧ q = 2} =
      {(3, 11, 5, 2), (7, 20, 4, 2)} := by
  sorry

/--
**Nagell–Ljunggren / Bugeaud–Mignotte Conjecture** (tuple form, Bugeaud–Mignotte 2002): the only
integer solutions $(x, y, n, q)$ to $\sum_{k=0}^{n-1} x^k = y^q$ with $x > 1$, $y > 1$, $n > 2$,
and $q \ge 2$ are $(18, 7, 3, 3)$, $(3, 11, 5, 2)$, and $(7, 20, 4, 2)$. (Wikipedia states the
equivalent perfect-power value form `nagell_ljunggren_conjecture.variants.perfect_power_values`.)
-/
@[category research open, AMS 11]
theorem nagell_ljunggren_conjecture :
    {(x, y, n, q) : ℕ × ℕ × ℕ × ℕ | IsNagellLjunggrenSolution x y n q} =
      {(18, 7, 3, 3), (3, 11, 5, 2), (7, 20, 4, 2)} := by
  sorry

/--
**Nagell–Ljunggren / Bugeaud–Mignotte Conjecture** (value form, OEIS A208242): the perfect powers
representable as repunits of length at least $3$ in some radix $x \ge 2$ equal $\{121, 343, 400\}$.
-/
@[category research open, AMS 11]
theorem nagell_ljunggren_conjecture.variants.perfect_power_values :
    {m : ℕ | ∃ x y n q : ℕ, IsNagellLjunggrenSolution x y n q ∧ y ^ q = m} =
      {121, 343, 400} := by
  sorry

end NagellLjunggrenConjecture
