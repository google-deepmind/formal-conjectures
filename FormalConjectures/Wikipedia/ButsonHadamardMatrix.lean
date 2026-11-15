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
# Butson-type Hadamard matrices

A *Butson-type Hadamard matrix* $H(k, n)$ (also written $\operatorname{BH}(n, k)$) is an
$n \times n$ complex matrix $M$ whose entries are $k$-th roots of unity ($M_{ij}^k = 1$) and whose
rows are mutually orthogonal in $\mathbb{C}^n$, so that $M M^* = n I_n$. At $k = 2$, $H(2, n)$
recovers real Hadamard matrices; at $k = 4$, $H(4, n)$ consists of matrices with entries in
$\{\pm 1, \pm i\}$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Butson-type_Hadamard_matrix)
- [Bu62] Butson, A. T. (1962). *Generalized Hadamard matrices*, Proc. Amer. Math. Soc. 13,
  894--898.
- [Tu70] Turyn, R. J. (1970). *Complex Hadamard matrices*, in Combinatorial Structures and their
  Applications (Calgary, 1969), Gordon and Breach, New York, 435--437.
- [Wi00] Winterhof, A. (2000). *On the non-existence of generalized Hadamard matrices*, J. Statist.
  Plann. Inference 84, 337--342.
- [dLF11] de Launey, W. and Flannery, D. L. (2011). *Algebraic Design Theory*, Mathematical Surveys
  and Monographs 175, Amer. Math. Soc.
-/

@[expose] public section

namespace ButsonHadamardMatrix

/-- `M` is a **Butson-type Hadamard matrix** $H(k, n)$ if every entry satisfies $z^k = 1$ and
$M M^* = n I_n$. -/
def IsButsonHadamard (k n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, M i j ^ k = 1) ∧ M * M.conjTranspose = (n : ℂ) • 1

/-- If $k \mid k'$, then every Butson-type Hadamard matrix $H(k, n)$ is also an $H(k', n)$
matrix. -/
@[category API, AMS 5 15]
theorem IsButsonHadamard.of_dvd {k k' n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∣ k') (hM : IsButsonHadamard k n M) :
    IsButsonHadamard k' n M := by
  rcases hk with ⟨d, rfl⟩
  exact ⟨fun i j => by rw [pow_mul, hM.1 i j, one_pow], hM.2⟩

/-- The $2 \times 2$ Sylvester matrix $\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$ realizes both
$H(2, 2)$ and $H(4, 2)$. -/
@[category test, AMS 5 15]
theorem exists_isButsonHadamard_four_two : ∃ M, IsButsonHadamard 4 2 M := by
  refine ⟨!![(1 : ℂ), 1; 1, -1], fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;> norm_num

/-- No $H(2, 3)$ (real $3 \times 3$ Hadamard matrix) exists because two rows in $\{\pm 1\}^3$ cannot
be orthogonal. -/
@[category test, AMS 5 15]
theorem not_exists_isButsonHadamard_two_three : ¬ ∃ M, IsButsonHadamard 2 3 M := by
  rintro ⟨M, hpow, horth⟩
  have hentry : ∀ i j, M i j = 1 ∨ M i j = -1 := fun i j => sq_eq_one_iff.mp (hpow i j)
  have hrow01 : M 0 0 * star (M 1 0) + M 0 1 * star (M 1 1) + M 0 2 * star (M 1 2) = 0 := by
    have h01 := congr_fun (congr_fun horth 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply] using h01
  rcases hentry 0 0 with a0 | a0 <;> rcases hentry 1 0 with b0 | b0 <;>
    rcases hentry 0 1 with a1 | a1 <;> rcases hentry 1 1 with b1 | b1 <;>
    rcases hentry 0 2 with a2 | a2 <;> rcases hentry 1 2 with b2 | b2 <;>
    rw [a0, b0, a1, b1, a2, b2] at hrow01 <;> norm_num at hrow01

/--
**Butson's prime divisibility theorem** [Bu62]: if $p$ is prime, $n \ge 2$, and a Butson-type
Hadamard matrix $H(p, n)$ exists, then $p \mid n$.

The hypothesis $n \ge 2$ excludes the trivial $1 \times 1$ matrix $[1]$, which satisfies
$H(p, 1)$ for every $p$.
-/
@[category research solved, AMS 5 15]
theorem butson_prime_divisibility {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    (hex : ∃ M, IsButsonHadamard p n M) :
    p ∣ n := by
  sorry

/--
**Complex Hadamard conjecture for fourth roots of unity** [Tu70, dLF11]: for every integer
$m \ge 1$, there exists a $2m \times 2m$ Butson-type Hadamard matrix $H(4, 2m)$ with entries in
$\{1, -1, i, -i\}$.

By Turyn's doubling construction [Tu70], an $H(4, 2m)$ matrix yields a real Hadamard matrix
$H(2, 4m)$, so this conjecture implies Hadamard's conjecture.
-/
@[category research open, AMS 5 15]
theorem butson_hadamard_fourth_roots_conjecture (m : ℕ) (hm : 1 ≤ m) :
    ∃ M, IsButsonHadamard 4 (2 * m) M := by
  sorry

end ButsonHadamardMatrix
