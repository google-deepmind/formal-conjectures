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
# Simple zeros of the Riemann zeta function on the critical line

*References:*
- [Cl26] Claude (Anthropic), *More than two thirds of the zeros of the Riemann zeta function are
  simple and on the critical line*, August 2026.
  [pdf](https://www-cdn.anthropic.com/95c246936988e43127bc6b2ceb7077c1dad2d68e.pdf),
  [Lean formalisation](https://github.com/anthropics/zeta-23-lean).
- [Wikipedia](https://en.wikipedia.org/wiki/Riemann_hypothesis#Zeros_on_the_critical_line)
- [J. J. Gebendorfer, Compatible local windows and a certified lower bound for simple critical-line zeros, audit revision 8 September 2026](https://doi.org/10.5281/zenodo.22661276), [cumulative variant and certificate-class source archive](https://github.com/user-attachments/files/33373834/Gebendorfer_WOWII_Zeta_Intake_2026-10-13.zip).

For a nontrivial zero `ρ = β + iγ` of `ζ` (or of a Dirichlet `L`-function) with multiplicity
`m_ρ`, and `0 ≤ T₁ < T₂`, write
- `N(T₁, T₂) = ∑_{T₁ < γ ≤ T₂} m_ρ` for the zeros counted with multiplicity,
- `N_d(T₁, T₂) = #{ρ : T₁ < γ ≤ T₂}` for the distinct zeros, and
- `Ns(T₁, T₂) = #{ρ : T₁ < γ ≤ T₂, β = 1/2, m_ρ = 1}` for the simple zeros on the critical line.

[Cl26, Theorem A] proves unconditionally that `Ns(T, 2T) ≥ (2/3 - o(1)) N(T, 2T)` and
`N_d(T, 2T) ≥ (5/6 - o(1)) N(T, 2T)`, improving to `2 - c_MT⁻¹ = 0.6725…` and
`(3 - c_MT⁻¹) / 2 = 0.8362…` with the Montgomery–Taylor window, where
`c_MT⁻¹ = 1/2 + cot(1/√2)/√2`; [Cl26, Theorem B] is the same for `L(s, χ)`, `χ` primitive.
-/

@[expose] public section

open Filter

namespace ZetaZeros

/-- The nontrivial zeros of `f` (those in the critical strip `0 < re s < 1`) with imaginary part
in `(T₁, T₂]`. -/
def nontrivialZeros (f : ℂ → ℂ) (T₁ T₂ : ℝ) : Set ℂ :=
  {s | f s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ T₁ < s.im ∧ s.im ≤ T₂}

/-- `N(T₁, T₂)`: the nontrivial zeros of `f` with imaginary part in `(T₁, T₂]`, counted with
multiplicity. -/
noncomputable def N (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ s ∈ nontrivialZeros f T₁ T₂, (analyticOrderAt f s).toNat

/-- `N_d(T₁, T₂)`: the number of distinct nontrivial zeros of `f` with imaginary part in
`(T₁, T₂]`. -/
noncomputable def Nd (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ := (nontrivialZeros f T₁ T₂).ncard

/-- `Ns(T₁, T₂)`: the number of simple zeros of `f` on the critical line with imaginary part in
`(T₁, T₂]`. -/
noncomputable def Ns (f : ℂ → ℂ) (T₁ T₂ : ℝ) : ℕ :=
  {s ∈ nontrivialZeros f T₁ T₂ | s.re = 1 / 2 ∧ analyticOrderAt f s = 1}.ncard

/-- The Montgomery–Taylor constant `c_MT = √2 tan(1/√2) / (1 + tan(1/√2)/√2)`, so that
`c_MT⁻¹ = 1/2 + cot(1/√2)/√2 = 1.3274…`. -/
noncomputable def montgomeryTaylorConst : ℝ := √2 * (1 / √2).tan / (1 + (1 / √2).tan / √2)

end ZetaZeros

open ZetaZeros

namespace riemannZeta

/-- At least two thirds of the nontrivial zeros of `ζ`, counted with
multiplicity, are simple and on the critical line [Cl26, Theorem A (i)]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/anthropics/zeta-23-lean/blob/v1.0/Zeta23/FinalMult.lean#L350"]
theorem simple_prop_two_thirds : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (2 / 3 - o T) * N riemannZeta T (2 * T) ≤ Ns riemannZeta T (2 * T) := by
  sorry

/-- At least five sixths of the nontrivial zeros of `ζ`, counted with
multiplicity, are distinct [Cl26, Theorem A (ii)]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/anthropics/zeta-23-lean/blob/v1.0/Zeta23/FinalMult.lean#L358"]
theorem distinct_prop_five_sixths : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (5 / 6 - o T) * N riemannZeta T (2 * T) ≤ Nd riemannZeta T (2 * T) := by
  sorry

/-- The proportion of simple zeros of `ζ` on the critical line is at least
`2 - c_MT⁻¹ = 0.6725…`. [Cl26, Theorem A]-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/anthropics/zeta-23-lean/blob/v1.0/Zeta23/ThmD/Mult.lean#L435"]
theorem simple_prop_montgomeryTaylor : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (2 - montgomeryTaylorConst⁻¹ - o T) * N riemannZeta T (2 * T) ≤
      Ns riemannZeta T (2 * T) := by
  sorry

/-- The proportion of distinct zeros of `ζ` is at least `(3 - c_MT⁻¹) / 2 = 0.8362…`,
[Cl26, Theorem A]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/anthropics/zeta-23-lean/blob/v1.0/Zeta23/ThmD/Mult.lean#L449"]
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
      ∀ T > 0, (c - o T) * N riemannZeta T (2 * T) ≤ Ns riemannZeta T (2 * T) := by
  sorry

/-- Almost all nontrivial zeros of `ζ` are simple and on the critical line. -/
@[category research open, AMS 11]
theorem simple_prop_one_hundred : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (1 - o T) * N riemannZeta T (2 * T) ≤ Ns riemannZeta T (2 * T) := by
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

/-- The cumulative proportion of simple critical-line zeros in (0,T] has
liminf at least the displayed exact rational, exceeding 0.6734775223. This
unconditional cumulative statement is distinct from the dyadic statements
above. The cited written proof uses the weighted pair-correlation formula and
Riemann–von Mangoldt; its finite certificate replay is not a Lean proof. -/
@[category research solved, AMS 11]
theorem simple_prop_cumulative_gebendorfer :
    (8269551442741204889710953 : ℝ) / 12278882618209750000000000 ≤
      Filter.liminf (fun T : ℝ => (Ns riemannZeta 0 T : ℝ) / N riemannZeta 0 T) atTop := by
  sorry

end riemannZeta

namespace DirichletCharacter

variable {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M}

/-- At least two thirds of the nontrivial zeros of `L(s, χ)`, `χ` primitive,
counted with multiplicity, are simple and on the critical line, [Cl26, Theorem B]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/anthropics/zeta-23-lean/blob/v1.0/Zeta23/ThmE/Mult.lean#L324"]
theorem simple_prop_two_thirds (hχ : χ.IsPrimitive) : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (2 / 3 - o T) * N (LFunction χ) T (2 * T) ≤ Ns (LFunction χ) T (2 * T) := by
  sorry

/-- At least five sixths of the nontrivial zeros of `L(s, χ)`, `χ` primitive,
counted with multiplicity, are distinct, [Cl26, Theorem B]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/anthropics/zeta-23-lean/blob/v1.0/Zeta23/ThmE/Mult.lean#L333"]
theorem distinct_prop_five_sixths (hχ : χ.IsPrimitive) : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (5 / 6 - o T) * N (LFunction χ) T (2 * T) ≤ Nd (LFunction χ) T (2 * T) := by
  sorry

/-- The proportion of simple zeros of `L(s, χ)`, `χ` primitive, on the critical line is at
least `2 - c_MT⁻¹ = 0.6725…`, [Cl26, Theorem B]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/anthropics/zeta-23-lean/blob/v1.0/Zeta23/ThmDE/Mult.lean#L429"]
theorem simple_prop_montgomeryTaylor (hχ : χ.IsPrimitive) :
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (2 - montgomeryTaylorConst⁻¹ - o T) * N (LFunction χ) T (2 * T) ≤
      Ns (LFunction χ) T (2 * T) := by
  sorry

/-- The proportion of distinct zeros of `L(s, χ)`, `χ` primitive, is at least
`(3 - c_MT⁻¹) / 2 = 0.8362…`, [Cl26, Theorem B]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/anthropics/zeta-23-lean/blob/v1.0/Zeta23/ThmDE/Mult.lean#L437"]
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
    ∀ T > 0, (c - o T) * N (LFunction χ) T (2 * T) ≤ Ns (LFunction χ) T (2 * T) := by
  sorry

/-- Almost all nontrivial zeros of `L(s, χ)`, `χ` primitive, are simple and on the critical
line. -/
@[category research open, AMS 11]
theorem simple_prop_one_hundred (hχ : χ.IsPrimitive) : ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
    ∀ T > 0, (1 - o T) * N (LFunction χ) T (2 * T) ≤ Ns (LFunction χ) T (2 * T) := by
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


namespace GebendorferZetaCertificateClass
open MeasureTheory

/-- The complete 25-mode cosine-window class, with free real integer modes 1–24. -/
noncomputable def window (c : Fin 24 → ℝ) (t : ℝ) : ℝ := by
  classical
  let a : ℝ := 1 / Real.sqrt 2
  let A := Real.sin a / a
  exact if t ∈ Set.Icc (-1/2 : ℝ) (1/2) then
    (Real.cos (Real.sqrt 2 * t) +
      ∑ j : Fin 24, c j * Real.cos (2 * Real.pi * (j.val + 1) * t)) / A else 0

/-- Normalization and nonnegativity of the actual window. Reality and evenness
are already encoded by its cosine formula and symmetric support. -/
def IsAdmissible (c : Fin 24 → ℝ) : Prop :=
  (∀ t, 0 ≤ window c t) ∧ (∫ t : ℝ, window c t) = 1

noncomputable def energyH (c : Fin 24 → ℝ) : ℝ :=
  2 - ((∫ u : ℝ, (window c u)^2) +
    ∫ u : ℝ, ∫ v : ℝ, |u - v| * window c u * window c v)

/-- Real Fourier transform; the absolute frequency is harmless because cosine
is even, and makes the symmetry of the actual Gram matrix explicit. -/
noncomputable def kernel (c : Fin 24 → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, window c t * Real.cos (2 * Real.pi * |x| * t)

def position {m : ℕ} (g : Fin (m - 1) → ℝ) (i : Fin m) : ℝ :=
  ∑ k : Fin (m - 1), if k.val < i.val then g k else 0

noncomputable def gram {m : ℕ} (c : Fin 24 → ℝ) (g : Fin (m - 1) → ℝ) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => kernel c (position g i - position g j)

noncomputable def clipped (t : ℝ) : ℝ := if t ≤ 2 then (t - 1)^2 else 2 * t - 3

/-- Trace of the clipped spectral function, with all Gram eigenvalues counted
with multiplicities. The Gram matrix is defined on the actual cumulative gaps. -/
noncomputable def clippedTrace {m : ℕ} (c : Fin 24 → ℝ) (g : Fin (m - 1) → ℝ) : ℝ :=
  let h : (gram c g).IsHermitian := by
    apply Matrix.ext
    intro i j
    simp [Matrix.conjTranspose_apply, gram, kernel, abs_sub_comm]
  ∑ i : Fin m, clipped (h.eigenvalues i)

/-- Every universal clipped-Gram certificate in the complete normalized
nonnegative 25-mode class with nonnegative gap prices and 0<R<m has value
strictly below 0.674034. This bounds the certificate class, not the actual
simple-zero proportion. It asserts neither sharpness nor attainment of the
class supremum. H may be replaced by any certified smaller real value. -/
@[category research solved, AMS 11 15]
theorem certificate_class_ceiling (c : Fin 24 → ℝ) (hc : IsAdmissible c)
    (m : ℕ) (hm : 2 ≤ m) (p : Fin (m - 1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (R : ℝ) (hR : 0 < R) (hRm : R < m) (H : ℝ) (hH : H ≤ energyH c)
    (hblock : ∀ g : Fin (m - 1) → ℝ, (∀ i, 0 ≤ g i) →
      R ≤ clippedTrace c g + ∑ i : Fin (m - 1), p i * g i) :
    ((m : ℝ) * H - ∑ i : Fin (m - 1), p i) / ((m : ℝ) - R) <
      (337017 : ℝ) / 500000 := by
  sorry

end GebendorferZetaCertificateClass
