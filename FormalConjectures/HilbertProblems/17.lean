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
module

public import FormalConjecturesUtil

/-!
# Hilbert's 17th problem

Let $f(x_1, \dots, x_n)$ be a multivariable polynomial with real coefficients that takes only
nonnegative values for all real inputs.
Hilbert's 17th problem asks whether there exist rational functions $g_1, \dots, g_m$ such that
$f = g_1^2 + g_2^2 + \cdots + g_m^2$. Resolved affirmatively by Artin in 1927.
*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hilbert%27s_seventeenth_problem)
- Motzkin, "The arithmetic-geometric inequality". In Shisha, Oved (ed.). Inequalities. Academic Press. pp. 205–224.
-/

@[expose] public section

open Real MvPolynomial

namespace Hilbert17

/--
Hilbert's 17th problem: every non-negative multivariate polynomial is a sum of
squares of rational functions.
-/
@[category research solved, AMS 12]
theorem hilbert_17th_problem {n : ℕ} (hn : 0 < n) (f : MvPolynomial (Fin n) ℝ)
    (h : ∀ x : Fin n → ℝ, 0 ≤ f.eval x) :
    ∃ (m : ℕ) (g : Fin m → MvRatFunc (Fin n) ℝ), algebraMap _ _ f = ∑ i, (g i) ^ 2 := by
  sorry

/--
The statement is false in general if we restrict to polynomials. The polynomial (by Motzkin)
$f(x, y) = x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1$ takes only nonnegative values but cannot be
written as a sum of squares of polynomials.
-/
noncomputable def f : MvPolynomial (Fin 2) ℝ :=
  X 0 ^ 4 * X 1 ^ 2 + X 0 ^ 2 * X 1 ^ 4 - 3 * X 0 ^ 2 * X 1 ^ 2 + 1

-- Proof taken from `motzkin_polynomial_nonneg` in mathlib
/-- The Motzkin polynomial is non-negative everywhere. -/
@[category textbook, AMS 12]
theorem f_nonneg : ∀ x y : ℝ, 0 ≤ f.eval ![x, y] := by
  intro x y
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, f, Fin.isValue, map_add, map_sub, map_mul, map_pow,
    eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, eval_ofNat, map_one]
  by_cases hx : x = 0
  · simp [hx]
  have h : 0 < (x ^ 2 + y ^ 2) ^ 2 := by positivity
  refine nonneg_of_mul_nonneg_left ?_ h
  have H : 0 ≤ (x ^ 3 * y + x * y ^ 3 - 2 * x * y) ^ 2 * (1 + x ^ 2 + y ^ 2)
    + (x ^ 2 - y ^ 2) ^ 2 := by positivity
  linear_combination H

set_option linter.unusedVariables false in
/-- The Motzkin polynomial cannot be written as a sum of squares of polynomials. -/
@[category textbook, AMS 12]
theorem f_not_sum_of_squares :
    ¬∃ (n : ℕ) (hn : 0 < n) (S : Fin n → MvPolynomial (Fin 2) ℝ), f = ∑ i, S i ^ 2 := by
  rintro ⟨n, _, S, hf⟩
  let mk (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b
  have hf_eq : f = monomial (mk 4 2) 1 + monomial (mk 2 4) 1 - monomial (mk 2 2) 3 + 1 := by
    simp [f, mk, X_pow_eq_monomial, monomial_mul, C_mul_monomial, ← map_ofNat C 3]
  have hf_supp {m} (hm : m ∈ f.support) : m = mk 4 2 ∨ m = mk 2 4 ∨ m = mk 2 2 ∨ m = 0 := by
    by_contra h; simp only [not_or] at h
    exact mem_support_iff.1 hm (by simp [hf_eq, coeff_monomial, coeff_one, eq_comm, h])
  have hsq (a : Fin 2 →₀ ℕ)
      (hu : ∀ i p, p.1 + p.2 = a + a → p.1 ∈ (S i).support → p.2 ∈ (S i).support → p = (a, a)) :
      f.coeff (a + a) = ∑ i, (S i).coeff a ^ 2 := by
    rw [hf, coeff_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_two (S i), coeff_mul, Finset.sum_eq_single (a, a), ← pow_two]
    · exact fun p hp hpm => by_contra fun h => hpm (hu i p (by simpa using hp)
        (mem_support_iff.2 (left_ne_zero_of_mul h)) (mem_support_iff.2 (right_ne_zero_of_mul h)))
    · simp
  let U : Finset (Fin 2 →₀ ℕ) := Finset.univ.biUnion fun i => (S i).support
  have hmem {i x} (hx : x ∈ (S i).support) : x ∈ U := Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩
  have hbound (w₀ w₁ B : ℤ) (hw₁ : w₁ ≠ 0)
      (hB : 4 * w₀ + 2 * w₁ ≤ 2 * B ∧ 2 * w₀ + 4 * w₁ ≤ 2 * B ∧ 0 ≤ 2 * B) :
      ∀ i m, m ∈ (S i).support → w₀ * m 0 + w₁ * m 1 ≤ B := fun i₀ m₀ hm₀ => by
    let φ (x : Fin 2 →₀ ℕ) : ℤ ×ₗ ℤ := toLex (w₀ * x 0 + w₁ * x 1, x 0)
    obtain ⟨m, hmU, hm_max⟩ := Finset.exists_max_image U φ ⟨m₀, hmem hm₀⟩
    have hm_supp : m + m ∈ f.support := mem_support_iff.2 <| ne_of_gt <| by
      rw [hsq m fun i p hsum hp1 hp2 => by
        simp only [Finsupp.ext_iff, Finsupp.add_apply, Fin.forall_fin_two] at hsum; zify at hsum
        have hφsum : φ p.1 + φ p.2 = φ m + φ m := ofLex.injective <| Prod.ext
          (by dsimp [φ]; linear_combination w₀ * hsum.1 + w₁ * hsum.2) hsum.1
        have hφeq := Prod.mk.inj (toLex.injective <| le_antisymm (hm_max _ (hmem hp1))
          (not_lt.1 fun hlt => (add_lt_add_of_lt_of_le hlt (hm_max _ (hmem hp2))).ne hφsum))
        have hp11 : (p.1 1 : ℤ) = m 1 :=
          mul_left_cancel₀ hw₁ (by linear_combination hφeq.1 - w₀ * hφeq.2)
        simp only [Prod.ext_iff, Finsupp.ext_iff, Fin.forall_fin_two]; omega]
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 hmU
      exact lt_of_lt_of_le (sq_pos_of_ne_zero (mem_support_iff.1 hj))
        (Finset.single_le_sum (fun i _ => sq_nonneg ((S i).coeff m)) (Finset.mem_univ j))
    have hmB : w₀ * (m + m) 0 + w₁ * (m + m) 1 ≤ 2 * B := by
      rcases hf_supp hm_supp with h | h | h | h <;> rw [h] <;> simp [mk] <;> linarith
    rcases Prod.Lex.le_iff.1 (hm_max _ (hmem hm₀)) with h | ⟨h, _⟩ <;>
      (simp only [φ, ofLex_toLex, Finsupp.add_apply, Nat.cast_add] at h hmB; linarith)
  have h1 := hbound 1 1 3 (by norm_num) (by norm_num)
  have h2 := hbound 1 (-2) 0 (by norm_num) (by norm_num)
  have h3 := hbound (-2) 1 0 (by norm_num) (by norm_num)
  have hcoeff := hsq (mk 1 1) fun i p hsum hp1 hp2 => by
    have := h1 i p.1 hp1; have := h2 i p.1 hp1; have := h3 i p.1 hp1
    have := h1 i p.2 hp2; have := h2 i p.2 hp2; have := h3 i p.2 hp2
    simp [Prod.ext_iff, Finsupp.ext_iff, Fin.forall_fin_two, mk] at hsum ⊢; omega
  have hneg : f.coeff (mk 1 1 + mk 1 1) = -3 := by
    simp [hf_eq, coeff_monomial, coeff_one, mk, Finsupp.ext_iff, Fin.forall_fin_two]
  linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg ((S i).coeff (mk 1 1))]

/--
For the polynomial version, Hilbert showed that every nonnegative homogeneous polynomial in
$n$ variables of degree $2d$ can be written as a sum of squares of polynomials if and only if
- $n = 1$
- $n = 2$
- $d = 1$
- $(n, d) = (3, 2)$.
-/
def Hilbert17thProblemHomogenousPoly (n d : ℕ) : Prop :=
  ∀ f : MvPolynomial (Fin n) ℝ, f.IsHomogeneous (2 * d) →
    (∀ x : Fin n → ℝ, 0 ≤ f.eval x) →
      ∃ (m : ℕ) (g : Fin m → MvPolynomial (Fin n) ℝ), f = ∑ i, (g i) ^ 2

@[category test, AMS 12]
theorem Hilbert17thProblemHomogenousPoly_zero_left (d : ℕ) :
    Hilbert17thProblemHomogenousPoly 0 d := by
  refine fun f hf hf₀ ↦ ⟨1, fun _ ↦ C √(f.coeff 0), ?_⟩
  have hfd := hf.totalDegree
  rw [f.eq_C_of_isEmpty] at hf₀ ⊢
  rw [Finset.sum_congr rfl fun _ _ ↦ (map_pow _ _ _).symm, Real.sq_sqrt <| by simpa using hf₀]
  simp

@[category test, AMS 12]
theorem Hilbert17thProblemHomogenousPoly_zero_right (n : ℕ) :
    Hilbert17thProblemHomogenousPoly n 0 := by
  intro f hf hf₀
  rcases eq_or_ne f 0 with (rfl | hf_zero); · exact ⟨0, 0, by simp⟩
  have hfd := f.totalDegree_eq_zero_iff_eq_C.1 <| by simpa using hf.totalDegree hf_zero
  use 1, fun _ ↦ C √(f.coeff 0)
  rw [Finset.sum_congr rfl fun _ _ ↦ (map_pow _ _ _).symm, Real.sq_sqrt <| by
    simpa [constantCoeff] using hf₀ 0]
  simpa using hfd

/--
Hilbert's 17th problem for homogeneous polynomials: characterization of dimensions and degrees
where non-negative polynomials are sums of squares of polynomials.
-/
@[category research solved, AMS 12]
theorem hilbert_17th_problem_poly {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    Hilbert17thProblemHomogenousPoly n d ↔ n = 1 ∨ n = 2 ∨ d = 1 ∨ n = 3 ∧ d = 2 := by
  sorry

end Hilbert17
