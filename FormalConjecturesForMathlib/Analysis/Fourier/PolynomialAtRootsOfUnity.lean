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

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# Discrete Parseval identity for complex polynomials at roots of unity

For a polynomial $P \in \mathbb{C}[X]$ of degree less than $N$ and $\omega$ a
primitive $N$-th root of unity in $\mathbb{C}$, the sum of the squared norms
$\|P(\omega^k)\|^2$ over $k \in \{0, \dots, N-1\}$ equals
$N \cdot \sum_i \|P_i\|^2$ where $P_i$ are the coefficients of $P$.

The core ingredient is the pair-form orthogonality of root-of-unity powers:
$\sum_{k < N} \omega^{ka} \cdot \overline{\omega^{kb}}$ equals $N$ when $a = b$
and $0$ otherwise (for $a, b < N$). The proof uses the geometric-series formula
applied to $\zeta = \omega^a \cdot \omega^{-b}$, which satisfies
$\zeta^N = 1$ and (in the $a \ne b$ case) $\zeta \ne 1$.
-/

namespace IsPrimitiveRoot

open Finset

/-- Pair-form orthogonality of root-of-unity powers: for $\omega$ a primitive
$N$-th root of unity in $\mathbb{C}$ and $a, b \in \{0, \dots, N-1\}$,
$\sum_{k < N} \omega^{ka} \cdot \overline{\omega^{kb}}$ equals $N$ if $a = b$
and $0$ otherwise. -/
theorem complex_sum_pow_mul_conj_pow
    {N : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω N)
    (hω_norm : ‖ω‖ = 1) {a b : ℕ} (ha : a < N) (hb : b < N) :
    ∑ k ∈ Finset.range N, ω ^ (k * a) * (starRingEnd ℂ) (ω ^ (k * b)) =
    if a = b then (N : ℂ) else 0 := by
  have hω_ne_zero : ω ≠ 0 := fun h => by simp [h] at hω_norm
  have hω_pow_N : ω ^ N = 1 := hω.pow_eq_one
  have hstar_ω : (starRingEnd ℂ) ω = ω⁻¹ := (RCLike.inv_eq_conj hω_norm).symm
  -- Rewrite each summand as a power of $\zeta = \omega^a \cdot (\omega^{-1})^b$.
  have hstar_pow : ∀ k, (starRingEnd ℂ) (ω ^ (k * b)) = (ω⁻¹) ^ (k * b) := by
    intro k; rw [map_pow, hstar_ω]
  set ζ : ℂ := ω ^ a * (ω⁻¹) ^ b with hζ_def
  have hsumm : ∀ k, ω ^ (k * a) * (starRingEnd ℂ) (ω ^ (k * b)) = ζ ^ k := by
    intro k
    rw [hstar_pow k, mul_comm k a, pow_mul, mul_comm k b, pow_mul, ← mul_pow, hζ_def]
  conv_lhs => rw [show (fun k => ω ^ (k * a) * (starRingEnd ℂ) (ω ^ (k * b))) =
                    (fun k => ζ ^ k) from funext hsumm]
  have hζN : ζ ^ N = 1 := by
    rw [hζ_def, mul_pow, ← pow_mul, ← pow_mul, mul_comm a N, mul_comm b N,
        pow_mul, pow_mul, hω_pow_N, inv_pow, hω_pow_N, inv_one, one_pow, one_pow,
        mul_one]
  split_ifs with hab
  · -- a = b: ζ = 1, sum = N.
    subst hab
    have hζ_one : ζ = 1 := by
      rw [hζ_def, ← mul_pow, mul_inv_cancel₀ hω_ne_zero, one_pow]
    simp [hζ_one]
  · -- a ≠ b: ζ ≠ 1, geom sum vanishes.
    have hζ_ne_one : ζ ≠ 1 := by
      intro h
      apply hab
      have hζ' : ω ^ a * (ω ^ b)⁻¹ = 1 := by rwa [hζ_def, inv_pow] at h
      have : ω ^ a = ω ^ b := by
        have hpow_b_ne : ω ^ b ≠ 0 := pow_ne_zero _ hω_ne_zero
        field_simp at hζ'; exact hζ'
      exact hω.pow_inj ha hb this
    rw [geom_sum_eq hζ_ne_one N, hζN, sub_self, zero_div]

end IsPrimitiveRoot

namespace Polynomial

open Finset

/-- Discrete Parseval identity for complex polynomials at primitive roots of
unity: for $P \in \mathbb{C}[X]$ of degree less than $N$ and $\omega$ a primitive
$N$-th root of unity, $\sum_{k < N} \|P(\omega^k)\|^2 = N \cdot \sum_{i < N} \|P_i\|^2$
where $P_i$ are the coefficients of $P$. -/
theorem sum_norm_sq_eval_primitiveRoot
    (P : ℂ[X]) {N : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω N)
    (hω_norm : ‖ω‖ = 1) (hdeg : P.natDegree < N) :
    ∑ k ∈ Finset.range N, ‖P.eval (ω ^ k)‖ ^ 2 =
    (N : ℝ) * ∑ i ∈ Finset.range N, ‖P.coeff i‖ ^ 2 := by
  -- $\|z\|^2 = z \cdot \overline{z}$ as a complex number.
  have hnorm_sq_cast : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [RCLike.mul_conj (K := ℂ)]; push_cast; rfl
  -- Expand $P(\omega^k) = \sum_i P_i \cdot \omega^{ki}$ and its conjugate.
  have hexpand : ∀ k, P.eval (ω ^ k) =
      ∑ i ∈ Finset.range N, P.coeff i * ω ^ (k * i) := by
    intro k
    rw [Polynomial.eval_eq_sum_range' hdeg]
    refine Finset.sum_congr rfl ?_
    intro i _; rw [pow_mul]
  have hexpand_conj : ∀ k, (starRingEnd ℂ) (P.eval (ω ^ k)) =
      ∑ j ∈ Finset.range N,
        (starRingEnd ℂ) (P.coeff j) * (starRingEnd ℂ) (ω ^ (k * j)) := by
    intro k
    rw [hexpand k, map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _; rw [map_mul]
  -- Cast both sides to $\mathbb{C}$ via `Complex.ofReal_injective`.
  apply_fun ((↑) : ℝ → ℂ) using Complex.ofReal_injective
  push_cast
  -- Convert each squared norm to a product with the conjugate.
  rw [show (∑ k ∈ Finset.range N, ((‖P.eval (ω ^ k)‖ : ℂ) ^ 2)) =
      ∑ k ∈ Finset.range N, P.eval (ω ^ k) * (starRingEnd ℂ) (P.eval (ω ^ k)) from
    Finset.sum_congr rfl fun k _ => by
      have := hnorm_sq_cast (P.eval (ω ^ k))
      push_cast at this; exact this]
  -- Expand into a triple sum.
  rw [show (∑ k ∈ Finset.range N, P.eval (ω ^ k) * (starRingEnd ℂ) (P.eval (ω ^ k))) =
      ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (P.coeff i * ω ^ (k * i)) *
        ((starRingEnd ℂ) (P.coeff j) * (starRingEnd ℂ) (ω ^ (k * j))) from
    Finset.sum_congr rfl fun k _ => by
      rw [hexpand_conj k, hexpand k, Finset.sum_mul_sum]]
  -- Swap sums so that k is innermost, then collapse via orthogonality + diagonal.
  calc ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (P.coeff i * ω ^ (k * i)) *
          ((starRingEnd ℂ) (P.coeff j) * (starRingEnd ℂ) (ω ^ (k * j)))
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
          (P.coeff i * ω ^ (k * i)) *
          ((starRingEnd ℂ) (P.coeff j) * (starRingEnd ℂ) (ω ^ (k * j))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (P.coeff i * (starRingEnd ℂ) (P.coeff j)) *
          (∑ k ∈ Finset.range N, ω ^ (k * i) * (starRingEnd ℂ) (ω ^ (k * j))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (P.coeff i * (starRingEnd ℂ) (P.coeff j)) * (if i = j then (N : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
        rw [hω.complex_sum_pow_mul_conj_pow hω_norm
              (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
    _ = ∑ i ∈ Finset.range N, (P.coeff i * (starRingEnd ℂ) (P.coeff i)) * (N : ℂ) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq (Finset.range N) i
              (fun j => P.coeff i * (starRingEnd ℂ) (P.coeff j) * (N : ℂ)), if_pos hi]
    _ = (N : ℂ) * ∑ i ∈ Finset.range N, ((‖P.coeff i‖ ^ 2 : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hnorm_sq_cast (P.coeff i)]; ring
    _ = (N : ℂ) * ∑ i ∈ Finset.range N, ((‖P.coeff i‖ : ℂ) ^ 2) := by
        congr 1; refine Finset.sum_congr rfl fun i _ => ?_; push_cast; rfl

end Polynomial
