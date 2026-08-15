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

/-!
# Hadamard's conjecture

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Hadamard_matrix#Hadamard_conjecture)
 - [Résolution d'une question relative aux déterminants](https://gallica.bnf.fr/ark:/12148/bpt6k486252g/f400.image.r) by *Jacques Hadamard*,  Bull. des sciences math., p.245, 1893
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

/--
Both definitions are equivalent.

TODO(firsching): complete and golf the proof
-/
@[category test, AMS 15]
theorem isHadamard_equiv_isHadamard' (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : IsHadamard' M ↔ IsHadamard M := by
  simp [IsHadamard, IsHadamard']
  intro h
  let N := M.transpose * M
  constructor
  · intro h
    have h_det : (M.transpose * M).det = n^((n : ℝ)) := by
      have : Matrix.diagonal (fun x : Fin n => (n : ℝ)) = (n : Matrix (Fin n) (Fin n) ℝ) := by
        rfl
      rw [h, ← this]
      norm_num
    simp only [Matrix.det_mul, Matrix.det_transpose] at h_det
    rw [← Real.sqrt_mul_self_eq_abs M.det, h_det]
    have : √(↑n ^ (n : ℝ)) = (↑n ^ (n : ℝ)) ^ ((1 : ℝ)/2) := by
      rw [Real.rpow_div_two_eq_sqrt]
      · simp only [Real.rpow_natCast, Real.rpow_one]
      · simp only [Real.rpow_natCast, Nat.cast_nonneg, pow_nonneg]
    rw [this]
    simp
    refine ((fun {x y z} hx hy hz ↦ (Real.eq_rpow_inv hx hy hz).mpr) ?_ ?_ ?_ ?_).symm
    · exact Real.rpow_nonneg (Nat.cast_nonneg' n) _
    · simp only [Nat.cast_nonneg, pow_nonneg]
    · norm_num
    · rw [← Real.rpow_mul <| Nat.cast_nonneg' n]
      norm_num
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
/-- Integer twin of `H12`: the same matrix over `ℤ`, where the orthogonality
arithmetic is kernel-decidable. The two `decide` lemmas below do all 144×12
products in `ℤ`; the `H12_map_row_*` lemmas transport entrywise to `ℝ`,
keeping every declaration inside the default `maxHeartbeats` budget. -/
private def N12 : Matrix (Fin 12) (Fin 12) ℤ :=
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

@[category API, AMS 15]
private lemma N12_orthogonal : N12.transpose * N12 = (12 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

@[category API, AMS 15]
private lemma N12_entries : ∀ i j, N12 i j ∈ ({1, -1} : Finset ℤ) := by decide

@[category API, AMS 15]
private lemma H12_map_row_0 (j : Fin 12) :
    H12 ⟨0, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨0, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_1 (j : Fin 12) :
    H12 ⟨1, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨1, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_2 (j : Fin 12) :
    H12 ⟨2, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨2, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_3 (j : Fin 12) :
    H12 ⟨3, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨3, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_4 (j : Fin 12) :
    H12 ⟨4, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨4, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_5 (j : Fin 12) :
    H12 ⟨5, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨5, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_6 (j : Fin 12) :
    H12 ⟨6, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨6, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_7 (j : Fin 12) :
    H12 ⟨7, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨7, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_8 (j : Fin 12) :
    H12 ⟨8, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨8, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_9 (j : Fin 12) :
    H12 ⟨9, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨9, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_10 (j : Fin 12) :
    H12 ⟨10, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨10, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_map_row_11 (j : Fin 12) :
    H12 ⟨11, by omega⟩ j = ((N12.map (⇑(Int.castRingHom ℝ))) ⟨11, by omega⟩ j) := by
  fin_cases j <;> norm_num [H12, N12]

@[category API, AMS 15]
private lemma H12_eq_map : H12 = N12.map (⇑(Int.castRingHom ℝ)) := by
  ext i j
  fin_cases i
  exacts [H12_map_row_0 j, H12_map_row_1 j, H12_map_row_2 j, H12_map_row_3 j,
    H12_map_row_4 j, H12_map_row_5 j, H12_map_row_6 j, H12_map_row_7 j,
    H12_map_row_8 j, H12_map_row_9 j, H12_map_row_10 j, H12_map_row_11 j]

@[category API, AMS 15]
private lemma H12_orthogonal : H12.transpose * H12 = (12 : ℝ) • 1 := by
  rw [H12_eq_map, ← Matrix.transpose_map,
    ← Matrix.map_mul (f := Int.castRingHom ℝ), N12_orthogonal]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/--
which satisfies the condition.
-/
@[category test, AMS 15]
theorem isHadamard_H12 : IsHadamard H12 := by
  constructor
  · intro i j
    rw [H12_eq_map]
    rcases Finset.mem_insert.mp (N12_entries i j) with h | h
    · rw [Matrix.map_apply, h]; norm_num
    · rw [Matrix.map_apply, Finset.mem_singleton.mp h]; norm_num
  · have hdet : H12.det ^ 2 = (12 : ℝ) ^ 12 := by
      have h1 : (H12.transpose * H12).det = (12 : ℝ) ^ 12 := by
        rw [H12_orthogonal, Matrix.det_smul, Matrix.det_one]
        simp
      rwa [Matrix.det_mul, Matrix.det_transpose, ← sq] at h1
    have habs : |H12.det| = (2985984 : ℝ) := by
      have h2 : ((12 : ℝ) ^ 12) = (2985984 : ℝ) ^ 2 := by norm_num
      rw [← Real.sqrt_sq_eq_abs, hdet, h2, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2985984)]
    rw [habs]
    rw [show ((12 : ℕ) : ℝ) / 2 = ((6 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    norm_num

/--
For all $k ≤ 166$, it is known there that there is a Hadamard matrix of size $4 * k$.
-/
@[category research solved, AMS 15]
theorem HadamardConjecture.variants.first_cases (k : ℕ) (h : k ≤ 166) :
    ∃ M, IsHadamard (n := 4 * k) M := by
  sorry

/--
The smallest order for which no Hadamard matrix is presently known is $668 = 4 * 167$.
-/
@[category research open, AMS 15]
theorem HadamardConjecture.variants.«167» : ∃ M, IsHadamard (n := 4 * 167) M := by
  sorry

end Hadamard
