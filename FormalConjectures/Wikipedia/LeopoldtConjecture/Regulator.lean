/-
Copyright 2025 The Formal Conjectures Authors.

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
import FormalConjectures.Wikipedia.LeopoldtConjecture
import FormalConjectures.Wikipedia.LeopoldtConjecture.PadicRegulator

/-!
# The regulator form for totally real fields

For totally real $K$ the matrix `Leopoldt.logMatrix` has $r + 1 = [K : \mathbb{Q}]$ columns and
its rows sum to zero (`sum_logMatrix`), so deleting any one column gives a square matrix whose
determinant is Washington's $p$-adic regulator `Leopoldt.padicRegulator`, well defined up to sign
(`padicRegulator_eq_or_eq_neg`).

This file proves $R_p(K) \neq 0$ equivalent to the full-rank form (`padicRegulator_ne_zero_iff`)
and hence to the elementary form (`leopoldtConjecture_iff_padicRegulator_ne_zero`).
-/

open Filter IsDedekindDomain NumberField NumberField.Units

open scoped NumberField

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
Each row of `logMatrix K p` sums to zero:
$\sum_\sigma \log_p \sigma(\varepsilon_i) = \log_p N_{K/\mathbb{Q}}(\varepsilon_i)
= \log_p(\pm 1) = 0$.
-/
@[category API, AMS 11]
theorem sum_logMatrix (i : Fin (rank K)) : ∑ σ, logMatrix K p i σ = 0 := by
  have hlog : ∀ σ : K →+* ℂ_[p], PadicExpLog.HasIwasawaLog p (σ (fundSystem K i : K)) := fun σ ↦
    PadicExpLog.PadicComplex.hasIwasawaLog ((map_ne_zero σ).2 (coe_ne_zero _))
  have hprod : ∏ σ : K →+* ℂ_[p], σ (fundSystem K i : K) =
      algebraMap ℚ ℂ_[p] (Algebra.norm ℚ (fundSystem K i : K)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ_[p]]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ_[p]) _ _ fun σ ↦ rfl
  have hnorm : |Algebra.norm ℚ (fundSystem K i : K)| = 1 := NumberField.Units.norm K _
  have hsq : (∏ σ : K →+* ℂ_[p], σ (fundSystem K i : K)) ^ 2 = 1 := by
    rw [hprod, ← map_pow, ← sq_abs, hnorm, one_pow, map_one]
  calc ∑ σ, logMatrix K p i σ
      = PadicExpLog.iwasawaLog p (∏ σ : K →+* ℂ_[p], σ (fundSystem K i : K)) :=
        (PadicExpLog.iwasawaLog_prod PadicExpLog.PadicComplex.norm_natCast_p_lt_one
          fun σ _ ↦ hlog σ).symm
    _ = 0 := PadicExpLog.iwasawaLog_of_pow_eq_one PadicExpLog.PadicComplex.norm_natCast_p_lt_one
          two_pos hsq

/-- The $p$-adic regulator is well defined up to sign. -/
@[category API, AMS 11]
theorem padicRegulator_eq_or_eq_neg (σ₀ σ₁ : K →+* ℂ_[p])
    (e₀ : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀})
    (e₁ : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₁}) :
    padicRegulator K p σ₀ e₀ = padicRegulator K p σ₁ e₁ ∨
      padicRegulator K p σ₀ e₀ = -padicRegulator K p σ₁ e₁ :=
  Matrix.det_submatrix_ne_eq_or_eq_neg (logMatrix K p) (sum_logMatrix K p) e₀ e₁

/-- The $p$-adic regulator is nonzero if and only if `logMatrix K p` has full rank $r$, i.e. if
and only if `leopoldt_conjecture.variants.padicRegulator` holds for `K`. -/
@[category API, AMS 11]
theorem padicRegulator_ne_zero_iff (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    padicRegulator K p σ₀ e ≠ 0 ↔ (logMatrix K p).rank = rank K := by
  rw [padicRegulator, Matrix.det_submatrix_ne_ne_zero_iff (logMatrix K p) (sum_logMatrix K p) e,
    Fintype.card_fin]

/--
For totally real $K$, the elementary form of Leopoldt's conjecture holds if and only if the
$p$-adic regulator does not vanish. This is `leopoldtConjecture_iff_rank` composed with
`padicRegulator_ne_zero_iff`.
-/
@[category API, AMS 11]
theorem leopoldtConjecture_iff_padicRegulator_ne_zero [IsTotallyReal K] (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    LeopoldtConjecture K p ↔ padicRegulator K p σ₀ e ≠ 0 :=
  (leopoldtConjecture_iff_rank K p).trans (padicRegulator_ne_zero_iff K p σ₀ e).symm

end Leopoldt
