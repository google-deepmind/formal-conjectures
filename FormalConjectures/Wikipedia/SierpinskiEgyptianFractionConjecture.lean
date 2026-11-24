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
Wacław Sierpiński [Si56] conjectured in 1956 that each integer $n \ge 2$ admits positive integers
$x, y, z \ge 1$ satisfying $5 / n = 1 / x + 1 / y + 1 / z$ (see
`Erdos242.erdos_242.variants.schinzel_generalization` for Andrzej Schinzel's asymptotic
generalization to arbitrary numerators). Sieve methods due to William A. Webb [We70] and Robert C.
Vaughan [Va70] establish sublinear upper bounds on the count of unexpandable denominators $n \le N$,
implying natural density zero, yet Sierpiński's conjecture for all $n \ge 2$ remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture#Generalizations)
- [Si56] W. Sierpiński (1956), *Mathesis* **65**, 16–32.
- [We70] W. A. Webb (1970), *Proc. Amer. Math. Soc.* **25**, 578–584.
- [Va70] R. C. Vaughan (1970), *Mathematika* **17**, 193–198.
-/

@[expose] public section

namespace SierpinskiEgyptianFractionConjecture

/-- `HasSierpinskiDecomposition n` holds when $5 / n = 1 / x + 1 / y + 1 / z$ for positive integers
$x, y, z \ge 1$. -/
def HasSierpinskiDecomposition (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧
    (5 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- Checks `HasSierpinskiDecomposition n` on small denominators $n = 2, 3, 4, 5$. -/
@[category test, AMS 11]
theorem sierpinski_small_cases :
    HasSierpinskiDecomposition 2 ∧ HasSierpinskiDecomposition 3 ∧
    HasSierpinskiDecomposition 4 ∧ HasSierpinskiDecomposition 5 := by
  refine ⟨⟨1, 1, 2, by omega, by omega, by omega, by norm_num⟩,
          ⟨1, 2, 6, by omega, by omega, by omega, by norm_num⟩,
          ⟨1, 5, 20, by omega, by omega, by omega, by norm_num⟩,
          ⟨2, 3, 6, by omega, by omega, by omega, by norm_num⟩⟩

/-- At $n = 1$, $5 / 1 = 5 > 1 + 1 + 1 = 3$, showing that `2 ≤ n` is sharp in
`sierpinski_egyptian_fraction_conjecture`. -/
@[category test, AMS 11]
theorem not_hasSierpinskiDecomposition_one :
    ¬ HasSierpinskiDecomposition 1 := by
  rintro ⟨x, y, z, hx, hy, hz, heq⟩
  have h1 : (1 : ℚ) / (x : ℚ) ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast hx) (by positivity)
  have h2 : (1 : ℚ) / (y : ℚ) ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast hy) (by positivity)
  have h3 : (1 : ℚ) / (z : ℚ) ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast hz) (by positivity)
  simp only [Nat.cast_one, div_one] at heq
  linarith

/-- **Webb–Vaughan Density Bound** [We70, Va70]: Denominators $n$ lacking a three-term unit-fraction
decomposition of $5 / n$ grow sublinearly up to $N$, hence have natural density $0$. -/
@[category research solved, AMS 11]
theorem sierpinski_counterexamples_hasDensity_zero :
    {n : ℕ | ¬ HasSierpinskiDecomposition n}.HasDensity 0 := by
  sorry

/-- **Sierpiński's $5 / n$ Conjecture** [Si56]: Each integer $n \ge 2$ admits positive integers
$x, y, z \ge 1$ satisfying $5 / n = 1 / x + 1 / y + 1 / z$. -/
@[category research open, AMS 11]
theorem sierpinski_egyptian_fraction_conjecture {n : ℕ} (hn : 2 ≤ n) :
    HasSierpinskiDecomposition n := by
  sorry

end SierpinskiEgyptianFractionConjecture
