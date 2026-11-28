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
# The Goreinov–Tyrtyshnikov–Zamarashkin conjecture

S. A. Goreinov, E. E. Tyrtyshnikov and N. L. Zamarashkin,
[*A theory of pseudoskeleton approximations*](https://doi.org/10.1016/S0024-3795(96)00301-1).
The authors also state the conjecture on [page 2 of *Pseudo-Skeleton Approximations*](https://www.inm.ras.ru/wp-content/uploads/library/Comp-Tech/psa-dan.pdf#page=2).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace GoreinovTyrtyshnikovZamarashkin

/-- Some $r$ distinct rows of $U$ form an invertible submatrix whose inverse has
Euclidean operator norm at most $\sqrt n$. -/
def HasSubmatrixWithBoundedInverse {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) : Prop :=
  ∃ rows : Fin r ↪ Fin n,
    let S := U.submatrix rows id
    S.det ≠ 0 ∧ ‖S⁻¹‖ ≤ Real.sqrt n

/-- Every real $n \times r$ matrix with orthonormal columns, $1 \le r < n$, has an
invertible $r \times r$ row submatrix whose inverse has spectral norm at most $\sqrt n$. -/
@[category research open, AMS 15 65]
theorem submatrix_inverse_bound {n r : ℕ} (hr : 0 < r) (hrn : r < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (hU : U.transpose * U = 1) :
    HasSubmatrixWithBoundedInverse U := by
  sorry

/-- For a single unit column, some entry has absolute value at least $1/\sqrt n$. -/
@[category textbook, AMS 15]
theorem one_column {n : ℕ} (hn : 0 < n) (U : Matrix (Fin n) (Fin 1) ℝ)
    (hU : U.transpose * U = 1) : HasSubmatrixWithBoundedInverse U := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsum : ∑ i, U i 0 ^ 2 = 1 := by
    simpa [Matrix.mul_apply, pow_two] using congrArg (fun A : Matrix (Fin 1) (Fin 1) ℝ ↦ A 0 0) hU
  have havg : ∑ _ : Fin n, (n : ℝ)⁻¹ ≤ ∑ i, U i 0 ^ 2 := by
    simp [hsum, nsmul_eq_mul, hn'.ne']
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  have hentry : (Real.sqrt n)⁻¹ ≤ |U i 0| := by
    simpa [Real.sqrt_inv, Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hi
  have hpos : 0 < |U i 0| := lt_of_lt_of_le (by positivity) hentry
  let rows : Fin 1 ↪ Fin n := ⟨fun _ ↦ i, fun a b _ ↦ Subsingleton.elim a b⟩
  refine ⟨rows, ?_, ?_⟩
  · rw [Matrix.det_eq_elem_of_subsingleton _ 0]
    exact abs_pos.mp hpos
  · rw [Matrix.inv_subsingleton, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    change ‖Ring.inverse (U i 0)‖ ≤ Real.sqrt n
    rw [Ring.inverse_eq_inv, norm_inv, Real.norm_eq_abs]
    exact (inv_le_comm₀ hpos (Real.sqrt_pos.2 hn')).2 hentry

end GoreinovTyrtyshnikovZamarashkin
