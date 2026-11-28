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
# Sharp subquadratic Lee constants

Xing Li compares the Schatten $p$-norm of a sum of matrices with that of the sum of their
moduli. Equation (1) defines their ratio. For $1<p<2$, Problem 4.2 asks for its supremum at
a fixed matrix order or over all positive orders. [X. Li, *Sharp Concave-Function Transfer
for Lee-Type Schatten Norm Inequalities*](https://arxiv.org/html/2608.25989#S4).
-/

@[expose] public section

namespace Arxiv.«2608.25989»

open scoped MatrixOrder Matrix.Norms.L2Operator NNReal

local notation "Mat" n:arg => Matrix (Fin n) (Fin n) ℂ

/-- The Schatten quantity $(\operatorname{tr}|A|^p)^{1/p}$ for $p>0$, a norm when $p\ge1$. -/
noncomputable def schattenNorm {n : ℕ} (p : ℝ) (A : Mat n) : ℝ :=
  (Matrix.trace (CFC.abs A ^ p)).re ^ p⁻¹

/-- Ratios for $m$ matrices of order $n$ in Li's equation (1), with zero denominators excluded. -/
def leeRatios (p : ℝ) (m n : ℕ) : Set ℝ :=
  {r | ∃ A : Fin m → Mat n, schattenNorm p (∑ j, CFC.abs (A j)) ≠ 0 ∧
    schattenNorm p (∑ j, A j) / schattenNorm p (∑ j, CFC.abs (A j)) = r}

def sharp_lee_constant.answer : ℝ → ℕ → ℝ := sorry

/-- Li's Problem 4.2, dimension-independent version. Determine the sharp linear constant for
$m$ summands and $1<p<2$, allowing matrices of every positive order. -/
@[category research open, question value, AMS 15 47]
theorem sharp_lee_constant {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) {m : ℕ} (hm : 0 < m) :
    IsLUB (⋃ n : ℕ, leeRatios p m (n + 1)) (sharp_lee_constant.answer p m) := by
  sorry

def sharp_lee_constant.variants.fixed_dimension.answer : ℝ → ℕ → ℕ → ℝ := sorry

/-- Li's fixed-dimension value question for the same ratio on complex $n\times n$ matrices. -/
@[category research open, question value, AMS 15 47]
theorem sharp_lee_constant.variants.fixed_dimension {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsLUB (leeRatios p m n) (fixed_dimension.answer p m n) := by
  sorry

/-- The identity as the only nonzero summand attains ratio one in every positive dimension. -/
@[category API, AMS 15]
theorem one_mem_leeRatios (p : ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    1 ∈ leeRatios p m n := by
  let i : Fin m := ⟨0, hm⟩
  let A : Fin m → Mat n := fun j ↦ if j = i then 1 else 0
  have hsum : ∑ j, A j = 1 := by simp [A]
  have habs : ∑ j, CFC.abs (A j) = 1 := by simp [A, apply_ite CFC.abs]
  have hnorm : schattenNorm p (1 : Mat n) ≠ 0 := by
    simp only [schattenNorm, CFC.abs_one, CFC.one_rpow, Matrix.trace_one, Fintype.card_fin,
      Complex.natCast_re]
    positivity
  exact ⟨A, by rwa [habs], by rw [hsum, habs, div_self hnorm]⟩

/-- For a single summand the only attainable ratio is one, in every positive dimension. -/
@[category API, AMS 15]
theorem leeRatios_one_summand (p : ℝ) {n : ℕ} (hn : 0 < n) : leeRatios p 1 n = {1} := by
  apply Set.Subset.antisymm _ (Set.singleton_subset_iff.mpr (one_mem_leeRatios p (by decide) hn))
  rintro r ⟨A, hA, rfl⟩
  have hmod : schattenNorm p (CFC.abs (A 0)) = schattenNorm p (A 0) := by
    simp only [schattenNorm, CFC.abs_of_nonneg _ (CFC.abs_nonneg _)]
  simp only [Fin.sum_univ_one, hmod, Set.mem_singleton_iff] at hA ⊢
  exact div_self hA

/-- The attainable ratios increase with the number of summands, by padding with zeros. -/
@[category API, AMS 15]
theorem leeRatios_mono (p : ℝ) (n : ℕ) : Monotone (fun m ↦ leeRatios p m n) := by
  apply monotone_nat_of_le_succ
  intro m
  rintro r ⟨A, hA, rfl⟩
  refine ⟨Fin.cons 0 A, ?_, ?_⟩
  · simpa [Fin.sum_univ_succ] using hA
  · simp [Fin.sum_univ_succ]

/-- The modulus of a one-by-one matrix is the scalar modulus of its entry. -/
@[category API, AMS 15]
theorem abs_apply_fin_one (A : Mat 1) : CFC.abs A 0 0 = (‖A 0 0‖ : ℂ) := by
  have h : A = algebraMap ℂ (Mat 1) (A 0 0) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.algebraMap_eq_diagonal]
  calc
    CFC.abs A 0 0 = CFC.abs (algebraMap ℂ (Mat 1) (A 0 0)) 0 0 :=
      congrArg (fun B : Mat 1 ↦ CFC.abs B 0 0) h
    _ = _ := by
      rw [CFC.abs_algebraMap]
      simp [Matrix.algebraMap_eq_diagonal]

/-- The Schatten norm of a one-by-one matrix is the modulus of its entry. -/
@[category API, AMS 15]
theorem schattenNorm_fin_one {p : ℝ} (hp : 0 < p) (A : Mat 1) :
    schattenNorm p A = ‖A 0 0‖ := by
  have h : CFC.abs A = algebraMap ℝ≥0 (Mat 1) ‖A 0 0‖₊ := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.algebraMap_eq_diagonal, IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
      NNReal.algebraMap_eq_coe] using abs_apply_fin_one A
  unfold schattenNorm
  rw [h, CFC.rpow_algebraMap]
  simp [Matrix.algebraMap_eq_diagonal, IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
    NNReal.algebraMap_eq_coe, NNReal.coe_rpow, hp.ne']

/-- In dimension one Li's ratio is the modulus of a sum divided by the sum of the moduli. -/
@[category API, AMS 15]
theorem mem_leeRatios_fin_one_iff {p r : ℝ} (hp : 0 < p) {m : ℕ} :
    r ∈ leeRatios p m 1 ↔ ∃ z : Fin m → ℂ, (∑ j, ‖z j‖) ≠ 0 ∧
      ‖∑ j, z j‖ / (∑ j, ‖z j‖) = r := by
  have numerator (A : Fin m → Mat 1) : schattenNorm p (∑ j, A j) = ‖∑ j, A j 0 0‖ := by
    rw [schattenNorm_fin_one hp, Matrix.sum_apply]
  have denominator (A : Fin m → Mat 1) :
      schattenNorm p (∑ j, CFC.abs (A j)) = ∑ j, ‖A j 0 0‖ := by
    rw [schattenNorm_fin_one hp, Matrix.sum_apply]
    simp only [abs_apply_fin_one, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
  constructor
  · rintro ⟨A, hA, hr⟩
    exact ⟨fun j ↦ A j 0 0, denominator A ▸ hA, by rwa [numerator, denominator] at hr⟩
  · rintro ⟨z, hz, hr⟩
    refine ⟨fun j ↦ Matrix.of fun _ _ ↦ z j, ?_, ?_⟩
    · rwa [denominator]
    · rwa [numerator, denominator]

/-- For at least two scalar summands the attainable ratios fill $[0,1]$. Each $r$ in the
interval is realized by the two real summands $1+r$ and $r-1$, followed by zeros. -/
@[category API, AMS 15]
theorem leeRatios_fin_one {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 2 ≤ m) :
    leeRatios p m 1 = Set.Icc 0 1 := by
  ext r
  constructor
  · intro hr
    obtain ⟨z, hz, rfl⟩ := (mem_leeRatios_fin_one_iff hp).mp hr
    have hpos : 0 < ∑ j, ‖z j‖ :=
      lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hz.symm
    exact ⟨div_nonneg (norm_nonneg _) hpos.le, (div_le_one hpos).mpr (norm_sum_le _ _)⟩
  · rintro ⟨hr₀, hr₁⟩
    apply leeRatios_mono p 1 hm
    apply (mem_leeRatios_fin_one_iff hp).mpr
    refine ⟨![((1 + r : ℝ) : ℂ), ((r - 1 : ℝ) : ℂ)], ?_, ?_⟩
    all_goals
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ 1 + r), abs_of_nonpos (by linarith : r - 1 ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ (1 + r) + (r - 1))]
    · linarith
    · field_simp
      ring

end Arxiv.«2608.25989»
