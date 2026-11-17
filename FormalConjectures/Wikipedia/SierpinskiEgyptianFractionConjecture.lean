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
# Sierpiński's $5/n$ Egyptian Fraction Conjecture

Analogously to the $4/n$ problem (`Erdos242.erdos_242` in `FormalConjectures.ErdosProblems.«242»`),
Wacław Sierpiński conjectured in 1956 that each integer $n \ge 2$ admits positive integers
$x, y, z \ge 1$ satisfying $5 / n = 1 / x + 1 / y + 1 / z$, and pairwise distinct denominators once
$n \ge 3$ (see `Erdos242.erdos_242.variants.schinzel_generalization` for Andrzej Schinzel's
asymptotic generalization to arbitrary numerators). Sieve bounds show that unexpandable denominators
have natural density zero, yet Sierpiński's conjecture for all $n \ge 2$ remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture#Generalizations)
- W. Sierpiński (1956), *Mathesis* **65**, 16–32.
- R. C. Vaughan (1970), *Mathematika* **17**, 193–198.
-/

@[expose] public section

namespace SierpinskiEgyptianFractionConjecture

/-- `HasSierpinskiDecomposition n` holds when $5 / n = 1 / x + 1 / y + 1 / z$ for positive integers
$x, y, z \ge 1$. -/
def HasSierpinskiDecomposition (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧
    (5 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- Strict variant requiring strictly increasing positive denominators $1 \le x < y < z$. -/
def HasStrictSierpinskiDecomposition (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (5 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- Checks `HasSierpinskiDecomposition 2` ($5 / 2 = 1 / 1 + 1 / 1 + 1 / 2$) and strict
decompositions for $n = 3, 4, 5$. -/
@[category test, AMS 11]
theorem sierpinski_small_cases :
    HasSierpinskiDecomposition 2 ∧ HasStrictSierpinskiDecomposition 3 ∧
    HasStrictSierpinskiDecomposition 4 ∧ HasStrictSierpinskiDecomposition 5 := by
  refine ⟨⟨1, 1, 2, by omega, by omega, by omega, by norm_num⟩,
          ⟨1, 2, 6, by omega, by omega, by omega, by norm_num⟩,
          ⟨1, 5, 20, by omega, by omega, by omega, by norm_num⟩,
          ⟨2, 3, 6, by omega, by omega, by omega, by norm_num⟩⟩

/-- At $n = 2$, $5 / 2 > 1 / 1 + 1 / 2 + 1 / 3 = 11 / 6$, ruling out pairwise distinct denominators
and motivating the $3 \le n$ bound in the strict variant. -/
@[category test, AMS 11]
theorem not_hasStrictSierpinskiDecomposition_two :
    ¬ HasStrictSierpinskiDecomposition 2 := by
  rintro ⟨x, y, z, hx, hxy, hyz, heq⟩
  have hy : 2 ≤ y := by omega
  have hz : 3 ≤ z := by omega
  have h1 : (1 : ℚ) / (x : ℚ) ≤ 1 := by
    have hx' : (1 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx
    exact div_le_one_of_le₀ hx' (by positivity)
  have h2 : (1 : ℚ) / (y : ℚ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hy)
  have h3 : (1 : ℚ) / (z : ℚ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hz)
  linarith

/-- **Vaughan's Density Bound (1970):** Denominators $n$ lacking a three-term unit-fraction
decomposition of $5 / n$ have natural density $0$. -/
@[category research solved, AMS 11]
theorem sierpinski_counterexamples_hasDensity_zero :
    {n : ℕ | ¬ HasSierpinskiDecomposition n}.HasDensity 0 := by
  sorry

/-- **Sierpiński's $5 / n$ Conjecture (1956):** Each integer $n \ge 2$ admits positive integers
$x, y, z \ge 1$ satisfying $5 / n = 1 / x + 1 / y + 1 / z$. -/
@[category research open, AMS 11]
theorem sierpinski_egyptian_fraction_conjecture {n : ℕ} (hn : 2 ≤ n) :
    HasSierpinskiDecomposition n := by
  sorry

/-- **Strict Sierpiński Conjecture:** Each integer $n \ge 3$ admits integers $1 \le x < y < z$
satisfying $5 / n = 1 / x + 1 / y + 1 / z$. -/
@[category research open, AMS 11]
theorem sierpinski_egyptian_fraction_conjecture.variants.strict {n : ℕ} (hn : 3 ≤ n) :
    HasStrictSierpinskiDecomposition n := by
  sorry

end SierpinskiEgyptianFractionConjecture
