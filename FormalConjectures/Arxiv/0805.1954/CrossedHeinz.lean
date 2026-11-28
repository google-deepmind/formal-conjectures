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
# Bourin's crossed-Heinz inequality

* J.-C. Bourin, *Matrix subadditivity inequalities and block-matrices*,
  [Question 4](https://arxiv.org/html/0805.1954).
* F. Kittaneh and É. Ricard prove the normalized bound for $1/4\le t\le3/4$.
  [On a question of Bourin](https://doi.org/10.1016/j.laa.2025.02.004)
* M. Sababheh and J.-C. Bourin prove the bound for $2\times2$ matrices.
  [Crossed-Heinz inequalities, Theorem 3.6](https://arxiv.org/html/2610.04567v2)
* Y. Tian and J. Xu give bounds for the operator and Frobenius norms in all dimensions.
  [Preprint, Theorems 1.1 and 1.2](https://arxiv.org/html/2611.22363v2)
-/

@[expose] public section

namespace Arxiv.«0805.1954»

open scoped MatrixOrder Matrix.Norms.L2Operator NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "M" => Matrix ι ι ℂ

/-- Bourin's bound at exponents $p,q$ for positive semidefinite complex matrices. -/
def CrossedHeinzBound (N : M → ℝ) (p q : ℝ) : Prop :=
  ∀ A B : M, 0 ≤ A → 0 ≤ B →
    N (A ^ p * B ^ q + B ^ p * A ^ q) ≤ N (A ^ (p + q) + B ^ (p + q))

/-- Bourin, Question 4. Does every unitarily invariant norm satisfy the crossed-Heinz
bound for every pair of nonnegative exponents? -/
@[category research open, question, AMS 15 47]
theorem crossed_heinz (N : Seminorm ℂ M) (hdef : ∀ X, N X = 0 → X = 0)
    (hunitary : ∀ (U V : Matrix.unitaryGroup ι ℂ) (X : M), N (U.val * X * V.val) = N X)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) : CrossedHeinzBound N p q := by
  sorry

/-- The original two-exponent bound is equivalent to the normalized inequality with
$0<t<1$. If either exponent is zero, the two sides agree. -/
@[category API, AMS 15 47]
theorem crossedHeinzBound_iff_normalized (N : M → ℝ) :
    (∀ p q : ℝ, 0 ≤ p → 0 ≤ q → CrossedHeinzBound N p q) ↔
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ A B : M, 0 ≤ A → 0 ≤ B →
        N (A ^ t * B ^ (1 - t) + B ^ t * A ^ (1 - t)) ≤ N (A + B) := by
  constructor
  · intro h t ht A B hA hB
    have hs : t + (1 - t) = 1 := by ring
    simpa only [hs, CFC.rpow_one A hA, CFC.rpow_one B hB] using
      h t (1 - t) ht.1.le (sub_nonneg.mpr ht.2.le) A B hA hB
  · intro h p q hp hq A B hA hB
    rcases hp.eq_or_lt with rfl | hp
    · simp [CFC.rpow_zero A hA, CFC.rpow_zero B hB, add_comm]
    rcases hq.eq_or_lt with rfl | hq
    · simp [CFC.rpow_zero A hA, CFC.rpow_zero B hB]
    have hs := add_pos hp hq
    have ht : p / (p + q) ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨div_pos hp hs, (div_lt_one hs).2 (lt_add_of_pos_right p hq)⟩
    have h₁ : (p + q) * (p / (p + q)) = p := by field_simp
    have h₂ : (p + q) * (1 - p / (p + q)) = q := by
      rw [mul_sub, mul_one, h₁]
      ring
    simpa only [CFC.rpow_rpow_of_exponent_nonneg, hs.le, ht.1.le, sub_nonneg.mpr ht.2.le,
      hA, hB, h₁, h₂] using
      h _ ht (A ^ (p + q)) (B ^ (p + q)) CFC.rpow_nonneg CFC.rpow_nonneg

/-- The crossed-Heinz bound holds for all nonnegative scalar multiples of the identity
and every complex seminorm. -/
@[category textbook, AMS 15 26]
theorem crossed_heinz.variants.scalar_matrices (N : Seminorm ℂ M) (a b : ℝ≥0)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    let A := algebraMap ℝ≥0 M a
    let B := algebraMap ℝ≥0 M b
    N (A ^ p * B ^ q + B ^ p * A ^ q) ≤ N (A ^ (p + q) + B ^ (p + q)) := by
  dsimp only
  simp only [CFC.rpow_algebraMap, ← map_mul, ← map_add]
  have hN (c : ℝ≥0) : N (algebraMap ℝ≥0 M c) = (c : ℝ) * N 1 := by
    rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul ℂ c (1 : M),
      map_smul_eq_mul]
    change ‖((c : ℝ) : ℂ)‖ * N 1 = _
    simp
  rw [hN, hN]
  apply mul_le_mul_of_nonneg_right _ (apply_nonneg N 1)
  apply NNReal.coe_le_coe.mpr
  rw [NNReal.rpow_add_of_nonneg a hp hq, NNReal.rpow_add_of_nonneg b hp hq]
  rcases le_total a b with hab | hba
  · exact mul_add_mul_le_mul_add_mul (NNReal.rpow_le_rpow hab hp) (NNReal.rpow_le_rpow hab hq)
  · exact mul_add_mul_le_mul_add_mul' (NNReal.rpow_le_rpow hba hp) (NNReal.rpow_le_rpow hba hq)

end Arxiv.«0805.1954»
