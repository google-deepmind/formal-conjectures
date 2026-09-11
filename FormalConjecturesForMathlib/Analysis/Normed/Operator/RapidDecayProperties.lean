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

public import FormalConjecturesForMathlib.Analysis.Normed.Operator.RapidDecay

/-!
# Further properties of rapidly decreasing operators

Approximation-number inequalities imply closure of rapidly decreasing operators under addition
and negation. Together with the composition bounds, these identify the generated ideal with
the set of rapidly decreasing operators. The final instance records compatibility of rational
scalars with multiplication in this ideal.
-/

@[expose] public section

open Filter
open scoped Topology

noncomputable section

namespace RapidDecayOperator

/-- Approximation errors are subadditive when the allowed ranks are added. -/
theorem approximationError_add (S T : BoundedOperator) (n m : ℕ) :
    approximationError (S + T) (n + m) ≤
      approximationError S n + approximationError T m := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨pS, qS, hS⟩ := exists_approximation_lt S n (half_pos hε)
  obtain ⟨pT, qT, hT⟩ := exists_approximation_lt T m (half_pos hε)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := m)
  let p : HilbertSpace →L[ℂ] EuclideanSpace ℂ (Fin (n + m)) :=
    e.symm.toContinuousLinearMap.comp (pS.prod pT)
  let q : EuclideanSpace ℂ (Fin (n + m)) →L[ℂ] HilbertSpace :=
    (qS.coprod qT).comp e.toContinuousLinearMap
  calc
    approximationError (S + T) (n + m) ≤ ‖S + T - q.comp p‖ := by
      apply csInf_le
      · exact ⟨0, by rintro _ ⟨r, rfl⟩; exact norm_nonneg _⟩
      · exact ⟨⟨p, q⟩, rfl⟩
    _ = ‖(S - qS.comp pS) + (T - qT.comp pT)‖ := by
      congr 1
      ext x
      simp [p, q, e]
      ring
    _ ≤ ‖S - qS.comp pS‖ + ‖T - qT.comp pT‖ := norm_add_le _ _
    _ ≤ approximationError S n + approximationError T m + ε := by
      nlinarith

/-- Allowing extra dimensions cannot increase the approximation error. -/
theorem approximationError_add_rank_le (T : BoundedOperator) (n m : ℕ) :
    approximationError T (n + m) ≤ approximationError T n := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨pT, qT, hT⟩ := exists_approximation_lt T n hε
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := m)
  let p : HilbertSpace →L[ℂ] EuclideanSpace ℂ (Fin (n + m)) :=
    e.symm.toContinuousLinearMap.comp (pT.prod 0)
  let q : EuclideanSpace ℂ (Fin (n + m)) →L[ℂ] HilbertSpace :=
    (qT.coprod 0).comp e.toContinuousLinearMap
  calc
    approximationError T (n + m) ≤ ‖T - q.comp p‖ := by
      apply csInf_le
      · exact ⟨0, by rintro _ ⟨r, rfl⟩; exact norm_nonneg _⟩
      · exact ⟨⟨p, q⟩, rfl⟩
    _ = ‖T - qT.comp pT‖ := by
      congr 1
      ext x
      simp [p, q, e]
    _ ≤ approximationError T n + ε := hT.le

/-- Approximation errors decrease with the permitted rank. -/
theorem approximationError_anti (T : BoundedOperator) :
    Antitone (approximationError T) := by
  intro n m hnm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact approximationError_add_rank_le T n d

/-- Rapid decay is preserved by addition. -/
theorem IsRapidlyDecaying.add {S T : BoundedOperator} (hS : IsRapidlyDecaying S)
    (hT : IsRapidlyDecaying T) : IsRapidlyDecaying (S + T) := by
  intro k
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpow : 0 < (2 : ℝ) ^ k := by positivity
  obtain ⟨NS, hNS⟩ := (Metric.tendsto_atTop.mp (hS k)) (ε / (2 * 2 ^ k)) (by positivity)
  obtain ⟨NT, hNT⟩ := (Metric.tendsto_atTop.mp (hT k)) (ε / (2 * 2 ^ k)) (by positivity)
  refine ⟨2 * max NS NT, fun r hr ↦ ?_⟩
  let d := r / 2
  have hd : max NS NT ≤ d := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
    omega
  have hdS : NS ≤ d := le_trans (le_max_left _ _) hd
  have hdT : NT ≤ d := le_trans (le_max_right _ _) hd
  have hs := hNS d hdS
  have ht := hNT d hdT
  rw [Real.dist_eq] at hs ht ⊢
  simp only [sub_zero] at hs ht
  rw [abs_of_nonneg (mul_nonneg (by positivity) (approximationError_nonneg S d))] at hs
  rw [abs_of_nonneg (mul_nonneg (by positivity) (approximationError_nonneg T d))] at ht
  rw [sub_zero, abs_of_nonneg (mul_nonneg (by positivity)
    (approximationError_nonneg (S + T) r))]
  have hdouble : d + d ≤ r := by
    dsimp [d]
    omega
  have herr : approximationError (S + T) r ≤
      approximationError S d + approximationError T d :=
    (approximationError_anti (S + T) hdouble).trans (approximationError_add S T d d)
  have hrank : ((r + 1 : ℕ) : ℝ) ^ k ≤ 2 ^ k * (((d + 1 : ℕ) : ℝ) ^ k) := by
    have hbase : ((r + 1 : ℕ) : ℝ) ≤ 2 * ((d + 1 : ℕ) : ℝ) := by
      norm_cast
      dsimp [d]
      omega
    calc
      ((r + 1 : ℕ) : ℝ) ^ k ≤ (2 * ((d + 1 : ℕ) : ℝ)) ^ k := by gcongr
      _ = 2 ^ k * (((d + 1 : ℕ) : ℝ) ^ k) := mul_pow _ _ _
  have hnonneg : 0 ≤ approximationError S d + approximationError T d :=
    add_nonneg (approximationError_nonneg S d) (approximationError_nonneg T d)
  calc
    ((r + 1 : ℕ) : ℝ) ^ k * approximationError (S + T) r
        ≤ ((r + 1 : ℕ) : ℝ) ^ k *
            (approximationError S d + approximationError T d) := by gcongr
    _ ≤ (2 ^ k * (((d + 1 : ℕ) : ℝ) ^ k)) *
            (approximationError S d + approximationError T d) := by gcongr
    _ = 2 ^ k * ((((d + 1 : ℕ) : ℝ) ^ k * approximationError S d) +
            (((d + 1 : ℕ) : ℝ) ^ k * approximationError T d)) := by ring
    _ < ε := by
      have hs' := mul_lt_mul_of_pos_left hs hpow
      have ht' := mul_lt_mul_of_pos_left ht hpow
      have hcancel : 2 ^ k * (ε / (2 * 2 ^ k)) = ε / 2 := by
        field_simp
      rw [hcancel] at hs' ht'
      nlinarith

/-- Negating an operator does not change its approximation errors. -/
@[simp] theorem approximationError_neg (T : BoundedOperator) (n : ℕ) :
    approximationError (-T) n = approximationError T n := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨p, q, hpq⟩ := exists_approximation_lt T n hε
    calc
      approximationError (-T) n ≤ ‖-T - (-q).comp p‖ := by
        apply csInf_le
        · exact ⟨0, by rintro _ ⟨r, rfl⟩; exact norm_nonneg _⟩
        · exact ⟨⟨p, -q⟩, rfl⟩
      _ = ‖T - q.comp p‖ := by
        rw [← norm_neg]
        congr 1
        ext x
        simp [sub_eq_add_neg, add_comm]
      _ ≤ approximationError T n + ε := hpq.le
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨p, q, hpq⟩ := exists_approximation_lt (-T) n hε
    calc
      approximationError T n ≤ ‖T - (-q).comp p‖ := by
        apply csInf_le
        · exact ⟨0, by rintro _ ⟨r, rfl⟩; exact norm_nonneg _⟩
        · exact ⟨⟨p, -q⟩, rfl⟩
      _ = ‖-T - q.comp p‖ := by
        rw [← norm_neg]
        congr 1
        ext x
        simp [sub_eq_add_neg, add_comm]
      _ ≤ approximationError (-T) n + ε := hpq.le

/-- Rapid decay is preserved by negation. -/
theorem IsRapidlyDecaying.neg {T : BoundedOperator} (hT : IsRapidlyDecaying T) :
    IsRapidlyDecaying (-T) := by
  intro k
  simpa using hT k

/-- The rapidly decreasing operators themselves form a two-sided ideal. -/
noncomputable def rapidIdeal : TwoSidedIdeal BoundedOperator :=
  TwoSidedIdeal.mk' {T | IsRapidlyDecaying T}
    isRapidlyDecaying_zero
    (fun hS hT ↦ hS.add hT)
    (fun hT ↦ hT.neg)
    (fun hT ↦ by simpa [ContinuousLinearMap.mul_def] using hT.comp_left _)
    (fun hT ↦ by simpa [ContinuousLinearMap.mul_def] using hT.comp_right _)

@[simp] theorem mem_rapidIdeal_iff (T : BoundedOperator) :
    T ∈ rapidIdeal ↔ IsRapidlyDecaying T := by
  simp [rapidIdeal, TwoSidedIdeal.mem_mk']

/-- The ideal generated by rapidly decreasing operators is exactly the ideal of rapidly
decreasing operators. -/
theorem ideal_eq_rapidIdeal : ideal = rapidIdeal := by
  apply le_antisymm
  · change TwoSidedIdeal.span {T | IsRapidlyDecaying T} ≤ rapidIdeal
    rw [TwoSidedIdeal.span_le]
    intro T hT
    exact mem_rapidIdeal_iff T |>.2 hT
  · intro T hT
    apply TwoSidedIdeal.subset_span
    exact mem_rapidIdeal_iff T |>.1 hT

theorem mem_ideal_iff (T : BoundedOperator) : T ∈ ideal ↔ IsRapidlyDecaying T := by
  rw [ideal_eq_rapidIdeal, mem_rapidIdeal_iff]

/-- Rational scalar multiplication associates with multiplication in the rapid-decay ideal. -/
instance : IsScalarTower ℚ ideal ideal where
  smul_assoc q x y := by
    apply Subtype.ext
    exact smul_mul_assoc q (x : BoundedOperator) (y : BoundedOperator)

end RapidDecayOperator
