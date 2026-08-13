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
import FormalConjectures.Wikipedia.Hadamard668

/-!
# Hadamard's conjecture

The concrete order-668 matrix is constructed over the integers in `Hadamard668`. That file proves
that every entry is a sign and that distinct columns are orthogonal. This file casts the entries to
real numbers and connects those two facts to the general definition of a Hadamard matrix below.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Hadamard_matrix#Hadamard_conjecture)
 - [Résolution d'une question relative aux déterminants](https://gallica.bnf.fr/ark:/12148/bpt6k486252g/f400.image.r) by *Jacques Hadamard*,  Bull. des sciences math., p.245, 1893
 - [Order-668 construction](https://x.com/__alpoge__/status/2087504785952182273)
   by *Levent Alpöge et al.* (2026)
-/

namespace Hadamard

/--
A square matrix $M$ with $±1$-entries that satisfies the equality $|M| ≤ n^\frac{n}{2}$ is called a *Hadamard matrix*.
-/
def IsHadamard {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    |M.det| = n ^ ((n : ℝ) / 2)

/--
Equivalently, a square matrix $M$ with $±1$-entries $|A| ≤ n^\frac{n}{2}.$ if it satisfies the equality
$M^TM = n \cdot 1$, where $1$ denotes the unit matrix.
-/
def IsHadamard' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    M.transpose * M = ↑n

/-- A sign matrix with orthogonal columns attains Hadamard's determinant bound. -/
@[category API, AMS 15]
theorem isHadamard_of_isHadamard' (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    IsHadamard' M → IsHadamard M := by
  rintro ⟨h_sign, h⟩
  refine ⟨h_sign, ?_⟩
  have h_det : (M.transpose * M).det = n ^ (n : ℝ) := by
    have : Matrix.diagonal (fun _ : Fin n => (n : ℝ)) =
        (n : Matrix (Fin n) (Fin n) ℝ) := by
      rfl
    rw [h, ← this]
    norm_num
  simp only [Matrix.det_mul, Matrix.det_transpose] at h_det
  rw [← Real.sqrt_mul_self_eq_abs M.det, h_det]
  have : √(↑n ^ (n : ℝ)) = (↑n ^ (n : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_div_two_eq_sqrt]
    · simp only [Real.rpow_natCast, Real.rpow_one]
    · simp only [Real.rpow_natCast, Nat.cast_nonneg, pow_nonneg]
  rw [this]
  simp
  refine ((fun {x y z} hx hy hz => (Real.eq_rpow_inv hx hy hz).mpr) ?_ ?_ ?_ ?_).symm
  · exact Real.rpow_nonneg (Nat.cast_nonneg' n) _
  · simp only [Nat.cast_nonneg, pow_nonneg]
  · norm_num
  · rw [← Real.rpow_mul <| Nat.cast_nonneg' n]
    norm_num

/--
Both definitions are equivalent.

TODO(firsching): complete and golf the reverse implication.
-/
@[category test, AMS 15]
theorem isHadamard_equiv_isHadamard' (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    IsHadamard' M ↔ IsHadamard M := by
  constructor
  · exact isHadamard_of_isHadamard' n M
  · sorry

/- Note: the conjecture was originally formulated by
Hadamard as a question: "For which values of $n=4k$ does
a Hadamard matrix exist." However the expectation seems
to be that all such matrices are Hadamard, and the
formalisation has been written with this in mind. -/

/--
There exists a Hadamard matrix for all $n = 4k$.
-/
@[category research open, AMS 15]
theorem HadamardConjecture (k : ℕ) : ∃ M, IsHadamard (n := 4 * k) M := by
  sorry

@[category test, AMS 15]
theorem exists_hadamard_zero : ∃ M, IsHadamard (n := 0) M := by
  use 0
  simp [IsHadamard]

/--
Hadamard constructs a 12 x 12 matrix ...
-/
def H12 : Matrix (Fin 12) (Fin 12) ℝ :=
!![  1,  1,  1,   1,  1,  1,   1,  1,  1,   1,  1,  1;
     1,  1,  1,  -1, -1, -1,  -1, -1, -1,   1,  1,  1;
     1,  1,  1,  -1, -1, -1,   1,  1,  1,  -1, -1, -1;
     1, -1, -1,   1, -1, -1,  -1,  1,  1,  -1,  1,  1;
     1, -1, -1,  -1,  1, -1,   1, -1,  1,   1, -1,  1;
     1, -1, -1,  -1, -1,  1,   1,  1, -1,   1,  1, -1;
     1, -1,  1,  -1,  1,  1,  -1,  1, -1,  -1, -1,  1;
     1, -1,  1,   1, -1,  1,  -1, -1,  1,   1, -1, -1;
     1, -1,  1,   1,  1, -1,   1, -1, -1,  -1,  1, -1;
     1,  1, -1,  -1,  1,  1,  -1, -1,  1,  -1,  1, -1;
     1,  1, -1,   1, -1,  1,   1, -1, -1,  -1, -1,  1;
     1,  1, -1,   1,  1, -1,  -1,  1, -1,   1, -1, -1 ]
/--
which satisfies the condition.
-/
@[category test, AMS 15]
theorem isHadamard_H12 : IsHadamard H12 := by
  sorry

/--
For all $k ≤ 166$, it is known there that there is a Hadamard matrix of size $4 * k$.
-/
@[category research solved, AMS 15]
theorem HadamardConjecture.variants.first_cases (k : ℕ) (h : k ≤ 166) :
    ∃ M, IsHadamard (n := 4 * k) M := by
  sorry

/-- The order-668 integer matrix from `Hadamard668`, cast entrywise to the real numbers. -/
def H668 : Matrix (Fin 668) (Fin 668) ℝ := fun i j => H668Int i j

/--
The integer proof gives two facts: every entry is $+1$ or $-1$, and multiplying the transpose by
the matrix gives 668 times the identity matrix. Casting those facts to the real numbers proves that
`H668` satisfies `IsHadamard'`.
-/
@[category test, AMS 15]
theorem isHadamard'_H668 : IsHadamard' H668 := by
  constructor
  · intro i j
    rcases H668Int_sign i j with h | h <;> simp [H668, h]
  · ext i j
    have h :=
      congrArg (fun A : Matrix (Fin 668) (Fin 668) ℤ => (A i j : ℝ)) H668Int_gram
    simp only [Matrix.mul_apply, Matrix.transpose_apply, H668, Int.cast_sum, Int.cast_mul]
      at h ⊢
    simpa [Matrix.ofNat_apply] using h

/-- The explicit matrix `H668` is a Hadamard matrix. -/
@[category test, AMS 15]
theorem isHadamard_H668 : IsHadamard H668 :=
  isHadamard_of_isHadamard' 668 H668 isHadamard'_H668

/--
There exists a Hadamard matrix of order $668 = 4 * 167$.

See the [2026 construction](https://x.com/__alpoge__/status/2087504785952182273).
-/
@[category research solved, AMS 15]
theorem HadamardConjecture.variants.«167» : ∃ M, IsHadamard (n := 4 * 167) M := by
  exact ⟨H668, isHadamard_H668⟩

end Hadamard
