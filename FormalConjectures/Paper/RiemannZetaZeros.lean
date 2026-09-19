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
import FormalConjecturesUtil

/-!
# Simple zeros of the Riemann zeta function on the critical line

*References:*
- [Cl26] Claude (Anthropic), *More than two thirds of the zeros of the Riemann zeta function are
  simple and on the critical line*, August 2026.
  [pdf](https://www-cdn.anthropic.com/95c246936988e43127bc6b2ceb7077c1dad2d68e.pdf),
  [Lean formalisation](https://github.com/anthropics/zeta-23-lean).
- [Wikipedia](https://en.wikipedia.org/wiki/Riemann_hypothesis#Zeros_on_the_critical_line)

For a nontrivial zero `ρ = β + iγ` of `ζ` (or of a Dirichlet `L`-function) with multiplicity
`m_ρ`, and `0 ≤ T₁ < T₂`, write
- `N(T₁, T₂) = ∑_{T₁ < γ < T₂} m_ρ` for the zeros counted with multiplicity,
- `N_d(T₁, T₂) = #{ρ : T₁ < γ < T₂}` for the distinct zeros, and
- `N₀simple(T₁, T₂) = #{ρ : T₁ < γ < T₂, β = 1/2, m_ρ = 1}` for the simple zeros on the critical line.

[Cl26, Theorem A] proves unconditionally that `N₀simple(T, 2T) ≥ (2/3 - o(1)) N(T, 2T)` and
`N_d(T, 2T) ≥ (5/6 - o(1)) N(T, 2T)`, improving to `2 - c_MT⁻¹ = 0.6725…` and
`(3 - c_MT⁻¹) / 2 = 0.8362…` with the Montgomery–Taylor window, where
`c_MT⁻¹ = 1/2 + cot(1/√2)/√2`; [Cl26, Theorem B] is the same for `L(s, χ)`, `χ` primitive. The
paper uses the window `T₁ < γ ≤ T₂`; the open window used here differs by `O(log T)` zeros,
which the `o(1)` absorbs.
-/

open Filter

namespace ZetaZeros

/-- The nontrivial zeros of `f` (those in the critical strip `0 < re s < 1`) with imaginary part
in `(T₁, T₂)`. -/
def nontrivialZeros (f : ℂ → ℂ) (T₁ T₂ : ℝ) : Set ℂ :=
  {s | f s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ T₁ < s.im ∧ s.im < T₂}

/-- `N(T₁, T₂)`: the nontrivial zeros of `f` with imaginary part in `(T₁, T₂)`, counted with
multiplicity. -/
noncomputable def N (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ s ∈ nontrivialZeros f T₁ T₂, (analyticOrderAt f s).toNat

/-- `N_d(T₁, T₂)`: the number of distinct nontrivial zeros of `f` with imaginary part in
`(T₁, T₂)`. -/
noncomputable def Nd (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ := (nontrivialZeros f T₁ T₂).ncard

/-- `N₀simple(T₁, T₂)`: the number of simple zeros of `f` on the critical line with imaginary part in
`(T₁, T₂)`. -/
noncomputable def N₀simple (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ :=
  {s ∈ nontrivialZeros f T₁ T₂ | s.re = 1 / 2 ∧ analyticOrderAt f s = 1}.ncard

/-- The Montgomery–Taylor constant `c_MT = √2 tan(1/√2) / (1 + tan(1/√2)/√2)`, so that
`c_MT⁻¹ = 1/2 + cot(1/√2)/√2 = 1.3274…`. -/
noncomputable def montgomeryTaylorConst : ℝ := √2 * (1 / √2).tan / (1 + (1 / √2).tan / √2)

end ZetaZeros

open ZetaZeros

namespace riemannZeta

/-- At least two thirds of the nontrivial zeros of `ζ`, counted with
multiplicity, are simple and on the critical line [Cl26, Theorem A (i)]. -/
@[category research solved, AMS 11]
theorem simple_prop_two_thirds : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (2 / 3 - o T) * N riemannZeta T (2 * T) ≤ N₀simple riemannZeta T (2 * T) := by
  sorry

/-- At least five sixths of the nontrivial zeros of `ζ`, counted with
multiplicity, are distinct [Cl26, Theorem A (ii)]. -/
@[category research solved, AMS 11]
theorem distinct_prop_five_sixths : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (5 / 6 - o T) * N riemannZeta T (2 * T) ≤ Nd riemannZeta T (2 * T) := by
  sorry

/-- The proportion of simple zeros of `ζ` on the critical line is at least
`2 - c_MT⁻¹ = 0.6725…`. [Cl26, Theorem A]-/
@[category research solved, AMS 11]
theorem simple_prop_montgomeryTaylor : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (2 - montgomeryTaylorConst⁻¹ - o T) * N riemannZeta T (2 * T) ≤
      N₀simple riemannZeta T (2 * T) := by
  sorry

/-- The proportion of distinct zeros of `ζ` is at least `(3 - c_MT⁻¹) / 2 = 0.8362…`,
[Cl26, Theorem A]. -/
@[category research solved, AMS 11]
theorem distinct_prop_montgomeryTaylor : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, ((3 - montgomeryTaylorConst⁻¹) / 2 - o T) * N riemannZeta T (2 * T) ≤
      Nd riemannZeta T (2 * T) := by
  sorry

/-- Is the proportion of simple zeros of `ζ` on the critical line unconditionally larger than
the Montgomery–Taylor bound `2 - c_MT⁻¹ = 0.6725…`? [Cl26, §7.2] puts the ceiling of its
method at about `0.682`. -/
@[category research open, AMS 11]
theorem simple_prop_lt : ∃ c > 2 - montgomeryTaylorConst⁻¹, ∃ o : ℝ → ℝ,
    o =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ T > 0, (c - o T) * N riemannZeta T (2 * T) ≤ N₀simple riemannZeta T (2 * T) := by
  sorry

/-- Almost all nontrivial zeros of `ζ` are simple and on the critical line. -/
@[category research open, AMS 11]
theorem simple_prop_one_hundred : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (1 - o T) * N riemannZeta T (2 * T) ≤ N₀simple riemannZeta T (2 * T) := by
  sorry

/-- Is the proportion of distinct zeros of `ζ` unconditionally larger than the Montgomery–Taylor
bound `(3 - c_MT⁻¹) / 2 = 0.8362…`? -/
@[category research open, AMS 11]
theorem distinct_prop_lt : ∃ c > (3 - montgomeryTaylorConst⁻¹) / 2, ∃ o : ℝ → ℝ,
    o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (c - o T) * N riemannZeta T (2 * T) ≤ Nd riemannZeta T (2 * T) := by
  sorry

/-- Almost all nontrivial zeros of `ζ` are simple. -/
@[category research open, AMS 11]
theorem distinct_prop_one_hundred : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (1 - o T) * N riemannZeta T (2 * T) ≤ Nd riemannZeta T (2 * T) := by
  sorry

end riemannZeta

namespace DirichletCharacter

variable {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M}

/-- At least two thirds of the nontrivial zeros of `L(s, χ)`, `χ` primitive,
counted with multiplicity, are simple and on the critical line, [Cl26, Theorem B]. -/
@[category research solved, AMS 11]
theorem simple_prop_two_thirds (hχ : χ.IsPrimitive) : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (2 / 3 - o T) * N (LFunction χ) T (2 * T) ≤ N₀simple (LFunction χ) T (2 * T) := by
  sorry

/-- At least five sixths of the nontrivial zeros of `L(s, χ)`, `χ` primitive,
counted with multiplicity, are distinct, [Cl26, Theorem B]. -/
@[category research solved, AMS 11]
theorem distinct_prop_five_sixths (hχ : χ.IsPrimitive) : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (5 / 6 - o T) * N (LFunction χ) T (2 * T) ≤ Nd (LFunction χ) T (2 * T) := by
  sorry

/-- The proportion of simple zeros of `L(s, χ)`, `χ` primitive, on the critical line is at
least `2 - c_MT⁻¹ = 0.6725…`, [Cl26, Theorem B]. -/
@[category research solved, AMS 11]
theorem simple_prop_montgomeryTaylor (hχ : χ.IsPrimitive) :
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (2 - montgomeryTaylorConst⁻¹ - o T) * N (LFunction χ) T (2 * T) ≤
      N₀simple (LFunction χ) T (2 * T) := by
  sorry

/-- The proportion of distinct zeros of `L(s, χ)`, `χ` primitive, is at least
`(3 - c_MT⁻¹) / 2 = 0.8362…`, [Cl26, Theorem B]. -/
@[category research solved, AMS 11]
theorem distinct_prop_montgomeryTaylor (hχ : χ.IsPrimitive) :
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, ((3 - montgomeryTaylorConst⁻¹) / 2 - o T) * N (LFunction χ) T (2 * T) ≤
      Nd (LFunction χ) T (2 * T) := by
  sorry

/-- Is the proportion of simple zeros of `L(s, χ)`, `χ` primitive, on the critical line
unconditionally larger than the Montgomery–Taylor bound `2 - c_MT⁻¹ = 0.6725…`? -/
@[category research open, AMS 11]
theorem simple_prop_lt (hχ : χ.IsPrimitive) : ∃ c > 2 - montgomeryTaylorConst⁻¹, ∃ o : ℝ → ℝ,
    o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (c - o T) * N (LFunction χ) T (2 * T) ≤ N₀simple (LFunction χ) T (2 * T) := by
  sorry

/-- Almost all nontrivial zeros of `L(s, χ)`, `χ` primitive, are simple and on the critical
line. -/
@[category research open, AMS 11]
theorem simple_prop_one_hundred (hχ : χ.IsPrimitive) : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (1 - o T) * N (LFunction χ) T (2 * T) ≤ N₀simple (LFunction χ) T (2 * T) := by
  sorry

/-- Is the proportion of distinct zeros of `L(s, χ)`, `χ` primitive, unconditionally larger than
the Montgomery–Taylor bound `(3 - c_MT⁻¹) / 2 = 0.8362…`? -/
@[category research open, AMS 11]
theorem distinct_prop_lt (hχ : χ.IsPrimitive) : ∃ c > (3 - montgomeryTaylorConst⁻¹) / 2,
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ T > 0, (c - o T) * N (LFunction χ) T (2 * T) ≤ Nd (LFunction χ) T (2 * T) := by
  sorry

/-- Almost all nontrivial zeros of `L(s, χ)`, `χ` primitive, are simple. -/
@[category research open, AMS 11]
theorem distinct_prop_one_hundred (hχ : χ.IsPrimitive) : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (1 - o T) * N (LFunction χ) T (2 * T) ≤ Nd (LFunction χ) T (2 * T) := by
  sorry

end DirichletCharacter
