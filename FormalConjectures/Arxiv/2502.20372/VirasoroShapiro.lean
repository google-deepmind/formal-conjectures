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
import FormalConjectures.Arxiv.«2502.20372».VenezianoPositivity

/-!
# Positivity of the Virasoro–Shapiro amplitude (Section 3.1)

*Reference:* [arxiv/2502.20372](https://arxiv.org/abs/2502.20372)
**Positivity of the Veneziano Amplitude in Ten Dimensions** by *Gareth Mansfield*, §3.1

The closed-string analogues of the Veneziano amplitude follow from KLT/double copy. The
type-II Virasoro–Shapiro amplitude (eq. 3.5)
$$A^{\mathrm{II}}(s,t) = \frac{\sin(\pi s)\sin(\pi t)}{\pi \sin(\pi(s+t))}\,A^0(s,t)^2
  = \frac{\Gamma(-s)\Gamma(-t)\Gamma(-u)}{\Gamma(1+s)\Gamma(1+t)\Gamma(1+u)}, \quad u = -s-t,$$
has residues (eq. 3.7) that are the *squares* of the open-string residues,
$$\operatorname{Res}_{s=n} A^{\mathrm{II}} = \Big(\frac{(t+1)_{(n-1)}}{n!}\Big)^{\!2},$$
while the heterotic amplitude (eq. 3.6) has
$$\operatorname{Res}_{s=n} A^{\mathrm{Het}}
  = \frac{(t+1)_{(n-1)}\,(t+2)_{(n+1)}}{n!\,(n+1)!}.$$
Mansfield deduces partial-wave positivity of both in `D ≤ 10` from the open-string result,
since products of positive Gegenbauer expansions are positive.

This is the shared statement for the uniqueness paper
`FormalConjectures/Arxiv/2508.09246/StringsFromAlmostNothing.lean`, whose nonplanar
bootstrap lands precisely on the Virasoro–Shapiro amplitude.
-/

namespace Arxiv.«2502.20372»

open Polynomial

/--
The type-II Virasoro–Shapiro residue at level `n` in the angular variable `x = 1 + 2t/n`:
the square of the open-string residue (eq. 3.7).
-/
noncomputable def vsResidueX (n : ℕ) : ℚ[X] := residueX n ^ 2

/--
The heterotic residue at level `n` in the angular variable `x = 1 + 2t/n` (eq. 3.7):
$(t+1)_{(n-1)} (t+2)_{(n+1)} / (n!\,(n+1)!)$ with `t = n (x - 1) / 2`.
-/
noncomputable def hetResidueX (n : ℕ) : ℚ[X] :=
  C (((n.factorial : ℚ) * (n + 1).factorial)⁻¹) *
    (∏ i ∈ Finset.range (n - 1), (C ((n : ℚ) / 2) * (X - 1) + C ((i : ℚ) + 1))) *
    (∏ i ∈ Finset.range (n + 1), (C ((n : ℚ) / 2) * (X - 1) + C ((i : ℚ) + 2)))

@[category test, AMS 81]
theorem vsResidueX_one : vsResidueX 1 = 1 := by
  simp [vsResidueX, residueX_one]

/--
**Type-II Virasoro–Shapiro positivity (§3.1).** In `D ≤ 10` the closed-string residues —
squares of the open-string residues — expand in the Gegenbauer spin basis with non-negative
coefficients. Follows from the Veneziano result via the double copy, since the Gegenbauer
linearization of a product of non-negative expansions is non-negative.
-/
@[category research solved, AMS 33 81]
theorem virasoro_shapiro_positivity {D : ℕ} (hD : 3 ≤ D) (hD10 : D ≤ 10) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ B : ℕ → ℚ, (∀ j, 0 ≤ B j) ∧
      vsResidueX n = ∑ j ∈ Finset.range (2 * n - 1), C (B j) * gegenbauer (lam D) j := by
  sorry

/--
**Heterotic positivity (§3.1).** The heterotic residues likewise have non-negative
partial-wave coefficients in `D ≤ 10`.
-/
@[category research solved, AMS 33 81]
theorem heterotic_positivity {D : ℕ} (hD : 3 ≤ D) (hD10 : D ≤ 10) {n : ℕ} (hn : 1 ≤ n) :
    ∃ B : ℕ → ℚ, (∀ j, 0 ≤ B j) ∧
      hetResidueX n = ∑ j ∈ Finset.range (2 * n + 1), C (B j) * gegenbauer (lam D) j := by
  sorry

/--
Heterotic positivity at level `n = 1` across `4 ≤ D ≤ 10`: the residue
`(t+2)(t+3)/2 = (x+3)(x+5)/8` decomposes into spins 0, 1, 2 with coefficients
`15/8 + 1/(16(λ+1))`, `1/(2λ)`, `1/(16λ(λ+1))`, all positive. A concrete verification of
`heterotic_positivity` (and of the `hetResidueX` definition) at the first level.
-/
@[category test, AMS 33 81]
theorem heterotic_positivity_one {D : ℕ} (hD : 4 ≤ D) :
    ∃ B : ℕ → ℚ, (∀ j, 0 ≤ B j) ∧
      hetResidueX 1 = ∑ j ∈ Finset.range 3, C (B j) * gegenbauer (lam D) j := by
  have hl := lam_pos hD
  refine ⟨fun j => if j = 0 then 15 / 8 + 1 / (16 * (lam D + 1))
                   else if j = 1 then 1 / (2 * lam D)
                   else if j = 2 then 1 / (16 * lam D * (lam D + 1)) else 0, ?_, ?_⟩
  · intro j
    dsimp only
    split
    · positivity
    · split
      · positivity
      · split
        · positivity
        · norm_num
  · apply Polynomial.funext
    intro x
    rw [eval_finset_sum]
    simp only [hetResidueX, Nat.sub_self, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, gegenbauer_zero, gegenbauer_one, gegenbauer_two, Finset.prod_range_succ,
      Finset.prod_range_zero, one_mul, Nat.factorial, eval_mul, eval_add, eval_sub, eval_C,
      eval_X, eval_one, eval_pow, reduceIte, Nat.one_ne_zero, Nat.reduceEqDiff,
      OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false]
    have h0 : lam D ≠ 0 := hl.ne'
    have h1 : lam D + 1 ≠ 0 := by positivity
    field_simp
    ring

/--
Type-II positivity at level `n = 2` across `4 ≤ D ≤ 10`: the squared residue `(x/2)² = x²/4`
decomposes into spins 0 and 2 with coefficients `1/(8(λ+1))` and `1/(8λ(λ+1))`, both positive.
A concrete verification of `virasoro_shapiro_positivity` at the first non-trivial level.
-/
@[category test, AMS 33 81]
theorem virasoro_shapiro_positivity_two {D : ℕ} (hD : 4 ≤ D) :
    ∃ B : ℕ → ℚ, (∀ j, 0 ≤ B j) ∧
      vsResidueX 2 = ∑ j ∈ Finset.range 3, C (B j) * gegenbauer (lam D) j := by
  have hl := lam_pos hD
  refine ⟨fun j => if j = 0 then 1 / (8 * (lam D + 1))
                   else if j = 2 then 1 / (8 * lam D * (lam D + 1)) else 0, ?_, ?_⟩
  · intro j
    dsimp only
    split
    · positivity
    · split
      · positivity
      · norm_num
  · apply Polynomial.funext
    intro x
    rw [eval_finset_sum]
    simp only [vsResidueX, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      gegenbauer_zero, gegenbauer_one, gegenbauer_two, residueX, Finset.prod_range_succ,
      Finset.prod_range_zero, one_mul, Nat.factorial, eval_mul, eval_add, eval_sub, eval_C,
      eval_X, eval_one, eval_pow, reduceIte]
    rw [if_neg (by decide : ¬ (1 : ℕ) = 0), if_neg (by decide : ¬ (1 : ℕ) = 2),
      if_neg (by decide : ¬ (2 : ℕ) = 0)]
    have h0 : lam D ≠ 0 := hl.ne'
    have h1 : lam D + 1 ≠ 0 := by positivity
    field_simp
    ring

/--
Type-II positivity at the critical level `n = 3` across `4 ≤ D ≤ 10`: the squared residue
`((9x²-1)/24)²` decomposes into spins 0, 2, 4 with explicit coefficients
`B₄ = 27/(128λ(λ+1)(λ+2)(λ+3))`, `B₂ = (21-2λ)/(128λ(λ+1)(λ+3))`,
`B₀ = (4λ³-12λ²+107λ+537)/(2304(λ+1)(λ+2)(λ+3))`, all non-negative for `λ ≤ 21/2`
(i.e. `D ≤ 24` — comfortably covering `D ≤ 10`).
-/
@[category test, AMS 33 81]
theorem virasoro_shapiro_positivity_three {D : ℕ} (hD : 4 ≤ D) (hD10 : D ≤ 10) :
    ∃ B : ℕ → ℚ, (∀ j, 0 ≤ B j) ∧
      vsResidueX 3 = ∑ j ∈ Finset.range 5, C (B j) * gegenbauer (lam D) j := by
  have hl := lam_pos hD
  have hDQ : (4 : ℚ) ≤ (D : ℚ) := by exact_mod_cast hD
  have hD10Q : (D : ℚ) ≤ 10 := by exact_mod_cast hD10
  have h21 : 0 < 21 - 2 * lam D := by rw [lam]; linarith
  set a := lam D with ha
  have h0 : a ≠ 0 := hl.ne'
  have h1 : a + 1 ≠ 0 := by positivity
  have h2 : a + 2 ≠ 0 := by positivity
  have h3 : a + 3 ≠ 0 := by positivity
  refine ⟨fun j => if j = 0 then (4*a^3 - 12*a^2 + 107*a + 537) / (2304*(a+1)*(a+2)*(a+3))
                   else if j = 2 then (21 - 2*a) / (128*a*(a+1)*(a+3))
                   else if j = 4 then 27 / (128*a*(a+1)*(a+2)*(a+3)) else 0, ?_, ?_⟩
  · intro j
    dsimp only
    split
    · have hnum : 0 < 4*a^3 - 12*a^2 + 107*a + 537 := by
        nlinarith [mul_nonneg hl.le (sq_nonneg (a - 3/2))]
      exact (div_pos hnum (by positivity)).le
    · split
      · exact (div_pos h21 (by positivity)).le
      · split
        · positivity
        · norm_num
  · apply Polynomial.funext
    intro x
    rw [eval_finset_sum]
    simp only [vsResidueX, residueX_three, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, gegenbauer_zero, gegenbauer_one, gegenbauer_two, eval_mul, eval_sub,
      eval_C, eval_X, eval_one, eval_pow, reduceIte]
    rw [if_neg (by decide : ¬ (1 : ℕ) = 0), if_neg (by decide : ¬ (1 : ℕ) = 2),
      if_neg (by decide : ¬ (1 : ℕ) = 4), if_neg (by decide : ¬ (2 : ℕ) = 0),
      if_neg (by decide : ¬ (3 : ℕ) = 0), if_neg (by decide : ¬ (3 : ℕ) = 2),
      if_neg (by decide : ¬ (3 : ℕ) = 4), if_neg (by decide : ¬ (4 : ℕ) = 0),
      if_neg (by decide : ¬ (4 : ℕ) = 2)]
    have e3 := congrArg (eval x) (gegenbauer_add_two a 1)
    have e4 := congrArg (eval x) (gegenbauer_add_two a 2)
    norm_num [eval_mul, eval_sub, eval_add, eval_C, eval_X, eval_pow, eval_one,
      gegenbauer_two, gegenbauer_one, gegenbauer_zero] at e3 e4
    rw [e4, e3]
    field_simp
    ring

end Arxiv.«2502.20372»
