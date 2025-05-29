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

import FormalConjectures.Util.ProblemImports

/-!
# Hadamard's conjecture

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Hadamard_matrix#Hadamard_conjecture)
 - [Résolution d'une question relative aux déterminants](https://gallica.bnf.fr/ark:/12148/bpt6k486252g/f400.image.r) by *Jacques Hadamard*,  Bull. des sciences math., p.245, 1893
-/

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

TOOD(firsching): complete and golf the proof
-/
@[category test]
example (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : IsHadamard' M ↔ IsHadamard M := by
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
      · simp only [Real.rpow_natCast, Nat.cast_nonneg, pow_nonneg, N]
    rw [this]
    simp
    refine ((fun {x y z} hx hy hz ↦ (Real.eq_rpow_inv hx hy hz).mpr) ?_ ?_ ?_ ?_).symm
    · exact Real.rpow_nonneg (Nat.cast_nonneg' n) _
    · simp only [Real.rpow_natCast, one_div, Nat.cast_nonneg, pow_nonneg, N]
    · norm_num
    · rw [← Real.rpow_mul <| Nat.cast_nonneg' n]
      norm_num
  · sorry


/--
Hadamard asks for which values of $n = 4k$ exists such a Matrix.
-/
@[category research open, AMS 15]
theorem HadamardConjecture (k : ℕ) : ∃ M, IsHadamard (n := 4 * k) M := by
  sorry

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
which satisifies the condition.
-/
@[category test]
example : IsHadamard H12 := by
  sorry

/--
The smallest order for which no Hadamard matrix is presently known is $668 = 4 * 167$.
-/
@[category research open, AMS 15]
theorem HadamardConjecture.variant : ∃ M, IsHadamard (n := 4 * 167) M := by
  sorry
