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
# Riemann Hypothesis and its generalizations

The Riemann Hypothesis asserts that all non-trivial zeros of the Riemann zeta function
$\zeta(s)$ have real part $\frac{1}{2}$. The trivial zeros are the negative even integers
$-2, -4, -6, \ldots$. The hypothesis is one of the seven Millennium Prize Problems
posed by the Clay Mathematics Institute.

The Generalized Riemann Hypothesis extends this to Dirichlet $L$-functions of primitive
Dirichlet characters.

Note: the **Extended Riemann Hypothesis** (ERH) for Dedekind zeta functions is intentionally
**not** stated here. Mathlib's `NumberField.dedekindZeta` is the naive Dirichlet series
(`LSeries`), not a meromorphic continuation; outside the region of absolute convergence
`tsum` returns junk `0`, producing spurious zeros that make the naive foramlisation of the
conjecture provably false. The ERH should be added once Mathlib provides a meromorphic
continuation of the Dedekind zeta function.

*References:*
- [The Clay Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf)
- [Wikipedia: Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis)
- [Wikipedia: Generalized Riemann hypothesis](https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis)
- [Wikipedia: Dedekind zeta function](https://en.wikipedia.org/wiki/Dedekind_zeta_function)
- J. Neukirch, *Algebraic Number Theory*, Springer (Grundlehren 322), 1999, Chapter VII, §5.
- D. A. Marcus, *Number Fields*, Springer (GTM 81), 1977, Chapter VII.
-/

@[expose] public section

namespace RiemannHypothesis

/-- The **Riemann Hypothesis**: all non-trivial zeros of the Riemann zeta function have real
part $\frac{1}{2}$. That is, if $\zeta(s) = 0$, $s \neq 1$, and $s$ is not a trivial zero
$-2(n+1)$ for some $n \in \mathbb{N}$, then $\operatorname{Re}(s) = \frac{1}{2}$.

This is the official Millennium Prize Problem as posed by the
[Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf).

This uses the `RiemannHypothesis` type from Mathlib, which is defined as
`∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2`. -/
@[category research open, AMS 11]
theorem riemannHypothesis : RiemannHypothesis := by
  sorry

end RiemannHypothesis

namespace GRH

/-- Let $\chi$ be a Dirichlet character, `trivialZeros` is the set of trivial zeros of the
Dirichlet $L$-function of $\chi$ which is always a set of non-positive integers.
- $\chi = 1$ then the Dirichlet $L$-function is the Riemann zeta function, having trivial
  zeroes at all negative even integers (exclude $0$).
- $\chi$ is odd, then the trivial zeroes are the negative odd integers.
- $\chi \neq 1$ is even, then the trivial zeroes are the non-positive even integers. -/
def trivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ :=
  if q = 1 then {-2 * (n + 1) | (n : ℕ) } else
    if χ.Odd then { -2 * n - 1 | (n : ℕ) } else
      { - 2 * n | (n : ℕ) }

/-- The **Generalized Riemann Hypothesis** asserts that all the non-trivial zeros of the
Dirichlet $L$-function $L(\chi, s)$ of a primitive Dirichlet character $\chi$ have real part
$\frac{1}{2}$. -/
@[category research open, AMS 11]
theorem generalized_riemann_hypothesis (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : ℂ) (hs : χ.LFunction s = 0)
    (hs_nontrivial : s ∉ Int.cast '' trivialZeros χ) :
    s.re = 1 / 2 := by
  sorry

/-- GRH for $\chi = 1$ is `RiemannHypothesis`. -/
@[category test, AMS 11]
theorem implies_riemannHypothesis :
    type_of% (generalized_riemann_hypothesis 1 1) ↔ RiemannHypothesis := by
  aesop (add simp [DirichletCharacter.isPrimitive_one_level_one, trivialZeros,
    RiemannHypothesis, riemannZeta_one_ne_zero])

/-- The completed $L$-function of a primitive Dirichlet character does not vanish for
$\operatorname{Re}(s) \le 0$ (away from the pole at $s = 0$ when $q = 1$). This follows from the
functional equation and the non-vanishing of $L(\chi^{-1}, s)$ on $\operatorname{Re}(s) \ge 1$. -/
@[category API, AMS 11]
theorem completedLFunction_ne_zero_of_re_nonpos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {s : ℂ} (hs : s.re ≤ 0) (h : s ≠ 0 ∨ q ≠ 1) :
    χ.completedLFunction s ≠ 0 := by
  intro h0
  have hχ' : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have hFE := hχ'.completedLFunction_one_sub s
  rw [inv_inv, h0, mul_zero] at hFE
  have hre : 1 ≤ (1 - s).re := by simpa using hs
  have hne : (1 - s) ≠ 0 := fun h1 ↦ by
    rw [h1, Complex.zero_re] at hre
    linarith
  have hL : χ⁻¹.LFunction (1 - s) = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inl hne), hFE, zero_div]
  refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ ?_ hre hL
  rcases h with h | h
  · exact Or.inr fun h1 ↦ h (by simpa using h1)
  · refine Or.inl fun h1 ↦ h ?_
    rw [inv_eq_one] at h1
    rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hχ
    exact hχ.symm

/-- The Generalized Riemann Hypothesis, as stated in `generalized_riemann_hypothesis` by excluding
the trivial zeros, is equivalent to the statement restricted to the critical strip: every zero of
$L(\chi, s)$ with $0 < \operatorname{Re}(s) < 1$, for $\chi$ primitive, has real part
$\frac{1}{2}$.

The forward direction says that every zero outside the critical strip is one of `trivialZeros`. -/
@[category test, AMS 11]
theorem generalized_riemann_hypothesis_iff_critical_strip :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ s : ℂ,
      0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2) ↔
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ s : ℂ,
      χ.LFunction s = 0 → s ∉ Int.cast '' trivialZeros χ → s.re = 1 / 2) := by
  constructor
  · intro H q _ χ hχ s hs hnt
    by_contra hre
    -- the zero is outside the open critical strip
    have hstrip : ¬ (0 < s.re ∧ s.re < 1) := fun h ↦ hre (H q χ hχ s h.1 h.2 hs)
    -- it is not to the right of the strip
    have hlt : s.re < 1 := by
      by_contra hge
      rw [not_lt] at hge
      by_cases h1 : χ ≠ 1 ∨ s ≠ 1
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 hge hs
      · rw [not_or, not_not, not_not] at h1
        obtain ⟨rfl, rfl⟩ := h1
        have hq : q = 1 := by
          rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
          exact hχ.symm
        subst hq
        rw [DirichletCharacter.LFunction_modOne_eq] at hs
        exact riemannZeta_one_ne_zero hs
    have hle : s.re ≤ 0 := by
      by_contra hpos
      exact hstrip ⟨not_le.mp hpos, hlt⟩
    -- so it is a zero of the gamma factor
    by_cases h0 : s ≠ 0 ∨ q ≠ 1
    · have hΛ := completedLFunction_ne_zero_of_re_nonpos hχ hle h0
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ h0, div_eq_zero_iff] at hs
      have hγ : χ.gammaFactor s = 0 := hs.resolve_left hΛ
      apply hnt
      rcases χ.even_or_odd with he | ho
      · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hγ
        obtain ⟨n, rfl⟩ := hγ
        by_cases hq : q = 1
        · have hn : n ≠ 0 := by
            rintro rfl
            simp [hq] at h0
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          exact ⟨-2 * (m + 1), by simp [trivialZeros, hq], by push_cast; ring⟩
        · have hodd : ¬ χ.Odd := fun ho ↦ χ.not_even_and_odd ⟨he, ho⟩
          exact ⟨-2 * n, by simp [trivialZeros, hq, hodd], by push_cast; ring⟩
      · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hγ
        obtain ⟨n, hn⟩ := hγ
        have hq : q ≠ 1 := by
          rintro rfl
          rw [DirichletCharacter.level_one χ] at ho
          exact (1 : DirichletCharacter ℂ 1).not_even_and_odd ⟨map_one _, ho⟩
        refine ⟨-2 * n - 1, by simp [trivialZeros, hq, ho], ?_⟩
        push_cast
        linear_combination -hn
    · rw [not_or, not_not, not_not] at h0
      obtain ⟨rfl, rfl⟩ := h0
      rw [DirichletCharacter.LFunction_modOne_eq, riemannZeta_zero] at hs
      norm_num at hs
  · intro H q _ χ hχ s hpos _ hs
    refine H q χ hχ s hs ?_
    rintro ⟨z, hz, rfl⟩
    have hz' : z ≤ 0 := by
      simp only [trivialZeros] at hz
      split_ifs at hz <;> obtain ⟨n, rfl⟩ := hz <;> omega
    have : ((z : ℂ)).re ≤ 0 := by simpa using hz'
    linarith

end GRH

/- NOTE: Extended Riemann Hypothesis
## Extended Riemann Hypothesis

The ERH for Dedekind zeta functions **cannot** currently be stated correctly because
`NumberField.dedekindZeta` in Mathlib is the naive `LSeries`, not the meromorphic
continuation.  Outside the region of absolute convergence (`re s > 1`), `tsum` returns
junk `0` for non-summable series.  A statement using the raw `dedekindZeta` therefore has
spurious "zeros" that make the conjecture provably **false**.

A correct formalisation requires a meromorphic continuation of the Dedekind zeta function
(analogous to how `ZMod.LFunction` extends the Dirichlet L-series).  Once Mathlib provides
this, the ERH should be added back here.
-/
