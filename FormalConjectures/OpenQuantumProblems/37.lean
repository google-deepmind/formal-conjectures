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
# Open Quantum Problem 37: Stronger submultiplicativity for the diamond norm

**Problem.** Does there exist an absolute constant $\alpha < 1$ such that the
submultiplicativity statement
$$\|\Theta \circ (\mathrm{id} - T)\|_\diamond \le
  \alpha \, \|\Theta\|_\diamond \, \|\mathrm{id} - T\|_\diamond$$
holds for all quantum channels $T$ over any finite-dimensional Hilbert space? Here
$\|\cdot\|_\diamond$ is the diamond norm (completely bounded trace norm) and $\Theta$ denotes
the transposition map $X \mapsto X^{\mathsf T}$, so $\|\Theta\|_\diamond$ equals the Hilbert
space dimension $d$.

## Background

Ordinary submultiplicativity of the diamond norm is the case $\alpha = 1$. Holevo and Werner
[HW01] used it to show that the $\varepsilon$-quantum capacity of a quantum channel $C$
satisfies $Q_\varepsilon(C) \le \log \|\Theta \circ C\|_\diamond$ whenever the error of the
coding scheme, measured as half the diamond-norm distance to the ideal channel, is at most
$\varepsilon < 1/2$. A constant $\alpha < 1$ that is uniform in the channel and in the
dimension extends this bound to all errors $\varepsilon < 1/(2\alpha)$. The original hope was
$\alpha = 1/2$, which would have given a strong converse rate; such a rate was later obtained
by different means by Müller-Hermes, Reeb and Wolf [MRW16].

The Open Quantum Problems page records the following partial results.
- In every fixed dimension $d$ some constant $\alpha(d) < 1$ suffices, by a continuity
  argument.
- For qubit channels $\|\Theta \circ (\mathrm{id} - T)\|_\diamond =
  \|\mathrm{id} - T\|_\diamond$, so $\alpha(2) = 1/2$ is the exact best constant in dimension $2$.
- For channels that are symmetric with respect to the orthogonal group $O(d)$, or with respect
  to representations of $SU(2)$ at the input and the output, the inequality holds with
  $\alpha = 1/2$.
- Random testing in dimensions at least $3$, with the diamond norms evaluated by the
  semidefinite programs of [Wat13], finds channels that need $\alpha > 1/2$, and unitary
  channels show that $\alpha > 0.63$ is required as the dimension grows [Fis16].

## Status

The problem is solved: Cha and Lee [CL26] proved that $\alpha = 1/\sqrt 2$ works for every
quantum channel in every dimension, and the Open Quantum Problems site lists Problem 37 among
the solved problems (solved by H. Cha, 2026). For a state $\rho$ on
$\mathbb{C}^d \otimes \mathbb{C}^d$ the proof combines three elementary facts: the bound
$\|Y\|_1 \le d \, \|Y\|_2$ for operators on a $d^2$-dimensional space, the invariance of the
Hilbert–Schmidt norm $\|\cdot\|_2$ under partial transposition, and the bound
$\|X\|_2 \le \|X\|_1 / \sqrt 2$ for traceless Hermitian $X$, applied to
$X = ((\mathrm{id} - T) \otimes \mathrm{id})(\rho)$.

The value of the optimal absolute constant $\alpha_*$ remains open. At present
$2/\pi \le \alpha_* \le 1/\sqrt 2$, and [CL26, Problem 1] asks to determine $\alpha_*$ and in
particular whether $\alpha_* < 1/\sqrt 2$.

## What this file formalizes

Matrices are complex matrices indexed by `Fin d`, and a `Superoperator d` is a linear map on
them. The file defines the trace norm `traceNorm`, the map `tensorId Φ m`
$= \Phi \otimes \mathrm{id}_m$, quantum channels `IsQuantumChannel`, the transposition map
`transposeMap d`, the diamond norm `diamondNorm`, and the predicate
`IsSubmultiplicativityConstant α` saying that the inequality of the problem holds with constant
$\alpha$ for all quantum channels in all dimensions.

- `stronger_submultiplicativity_diamond_norm` is the problem as posed (solved, the answer is
  yes).
- `stronger_submultiplicativity_diamond_norm.variants.inv_sqrt_two` and
  `stronger_submultiplicativity_diamond_norm.variants.hermitian_preserving` state the theorem
  of Cha and Lee, `stronger_submultiplicativity_diamond_norm.variants.two_div_pi_le` the lower
  bound $2/\pi$, and `stronger_submultiplicativity_diamond_norm.variants.qubit` the qubit case.
- `stronger_submultiplicativity_diamond_norm.variants.lt_inv_sqrt_two` and
  `optimal_submultiplicativity_constant` are the open problem of [CL26] on the optimal
  constant.

The definitions are tested by proved statements. Among them are the singular value formula
`traceNorm_eq_sum_sqrt_eigenvalues`, the tensor product rule `tensorId_kronecker`, the
boundedness `bddAbove_diamondNorm` of the set whose supremum is the diamond norm, ordinary
submultiplicativity `diamondNorm_comp_le`, the value `diamondNorm_transposeMap` of
$\|\Theta\|_\diamond$, the fact `not_isCompletelyPositive_transposeMap` that transposition is
not completely positive, the positivity `IsSubmultiplicativityConstant.pos` of every admissible
constant, and the existence `exists_isLeast_isSubmultiplicativityConstant` of the optimal
constant.

## References

- Open Quantum Problems, Problem 37:
  <https://oqp.iqoqi.oeaw.ac.at/stronger-submultiplicativity-for-the-diamond-norm>
- List of solved Open Quantum Problems:
  <https://oqp.iqoqi.oeaw.ac.at/solved-quantum-problems>
- Formal Conjectures issue #3454:
  <https://github.com/google-deepmind/formal-conjectures/issues/3454>
- [HW01] A. S. Holevo and R. F. Werner,
  *Evaluating capacities of bosonic Gaussian channels*,
  Phys. Rev. A 63, 032312 (2001),
  [arXiv:quant-ph/9912067](https://arxiv.org/abs/quant-ph/9912067).
- [Wat13] J. Watrous,
  *Simpler semidefinite programs for completely bounded norms*,
  Chicago J. Theoret. Comput. Sci. 2013, Article 8, 1-19,
  [arXiv:1207.5726](https://arxiv.org/abs/1207.5726).
- [Fis16] D. Fischer,
  *Quantum capacity bounds via semidefinite programming*,
  Bachelor's thesis, Leibniz University of Hannover (2016).
- [MRW16] A. Müller-Hermes, D. Reeb, and M. M. Wolf,
  *Positivity of linear maps under tensor powers*,
  J. Math. Phys. 57, 015202 (2016), [arXiv:1502.05630](https://arxiv.org/abs/1502.05630).
- [CL26] H. Cha and J. Lee,
  *Refining transposition bounds from traceless quantum perturbations*,
  [arXiv:2602.17748](https://arxiv.org/abs/2602.17748) (2026). The first version, by H. Cha
  alone, is titled *A dimension-independent strict submultiplicativity for the transposition
  map in diamond norm*.
- [Tom83] J. Tomiyama,
  *On the transpose map of matrix algebras*,
  Proc. Amer. Math. Soc. 88, 635-638 (1983).
- [Wat18] J. Watrous,
  *The Theory of Quantum Information*, Cambridge University Press (2018), Section 3.3.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section

namespace OpenQuantumProblem37

/- ## The trace norm -/

section TraceNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **trace norm** (Schatten $1$-norm) $\|X\|_1 = \operatorname{tr} \sqrt{X^\dagger X}$ of a
complex square matrix. Here `CFC.sqrt` is the positive semidefinite square root, so
`CFC.sqrt (Xᴴ * X)` is the absolute value $|X|$, whose trace is a nonnegative real number. -/
def traceNorm (X : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (Xᴴ * X)).trace.re

/-- The trace norm is the trace of the absolute value `CFC.abs X`. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_eq_trace_abs (X : Matrix n n ℂ) : traceNorm X = (CFC.abs X).trace.re := rfl

/-- The trace norm of the zero matrix is $0$. -/
@[simp, category API, AMS 46 47 81 94]
lemma traceNorm_zero : traceNorm (0 : Matrix n n ℂ) = 0 := by
  simp [traceNorm]

/-- The trace norm is nonnegative. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_nonneg (X : Matrix n n ℂ) : 0 ≤ traceNorm X :=
  (RCLike.nonneg_iff.mp (CFC.abs_nonneg X).posSemidef.trace_nonneg).1

/-- The trace norm is absolutely homogeneous: $\|c X\|_1 = |c| \, \|X\|_1$. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_smul (c : ℂ) (X : Matrix n n ℂ) : traceNorm (c • X) = ‖c‖ * traceNorm X := by
  simp [traceNorm_eq_trace_abs, CFC.abs_smul]

/-- On positive semidefinite matrices the trace norm is the trace. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_posSemidef {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    traceNorm X = X.trace.re := by
  rw [traceNorm_eq_trace_abs, CFC.abs_of_nonneg X hX.nonneg]

/-- A matrix with $U^\dagger U = 1$, i.e. a unitary matrix, has trace norm equal to the
dimension. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_of_conjTranspose_mul_self_eq_one {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    traceNorm U = Fintype.card n := by
  rw [traceNorm, hU, CFC.sqrt_one]
  simp

/-- The trace norm of the $d \times d$ identity matrix is $d$. -/
@[category test, AMS 46 47 81 94]
theorem traceNorm_one (d : ℕ) : traceNorm (1 : Matrix (Fin d) (Fin d) ℂ) = d := by
  simpa using traceNorm_of_conjTranspose_mul_self_eq_one
    (show (1 : Matrix (Fin d) (Fin d) ℂ)ᴴ * 1 = 1 by simp)

/-- The trace of the square root of a positive semidefinite matrix is the sum of the square
roots of its eigenvalues. -/
@[category API, AMS 46 47 81 94]
lemma trace_sqrt_eq_sum_sqrt_eigenvalues {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (CFC.sqrt A).trace = ∑ i, ((√(hA.1.eigenvalues i) : ℝ) : ℂ) := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A, hA.1.cfc_eq, IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, trace_mul_cycle]
  simp [trace_diagonal, max_eq_left (hA.eigenvalues_nonneg _)]

/-- The trace norm is the sum of the singular values, i.e. of the square roots of the
eigenvalues of $X^\dagger X$. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_eq_sum_sqrt_eigenvalues (X : Matrix n n ℂ) :
    traceNorm X = ∑ i, √((isHermitian_conjTranspose_mul_self X).eigenvalues i) := by
  rw [traceNorm, trace_sqrt_eq_sum_sqrt_eigenvalues (posSemidef_conjTranspose_mul_self X)]
  simp

/-- The squared **Hilbert–Schmidt norm** (Frobenius norm)
$\|X\|_2^2 = \operatorname{tr}(X^\dagger X)$. -/
def hsNormSq (X : Matrix n n ℂ) : ℝ :=
  (Xᴴ * X).trace.re

omit [DecidableEq n] in
/-- The squared Hilbert–Schmidt norm is the sum of the squared absolute values of the
entries. -/
@[category API, AMS 46 47 81 94]
lemma hsNormSq_eq_sum (X : Matrix n n ℂ) : hsNormSq X = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Finset.sum_comm]
  simp [hsNormSq, trace, mul_apply, Complex.conj_mul', ← Complex.ofReal_pow]

/-- The squared Hilbert–Schmidt norm is the sum of the eigenvalues of $X^\dagger X$, i.e. of
the squared singular values. -/
@[category API, AMS 46 47 81 94]
lemma hsNormSq_eq_sum_eigenvalues (X : Matrix n n ℂ) :
    hsNormSq X = ∑ i, (isHermitian_conjTranspose_mul_self X).eigenvalues i := by
  rw [hsNormSq, (isHermitian_conjTranspose_mul_self X).trace_eq_sum_eigenvalues]
  simp

/-- The Hilbert–Schmidt norm is dominated by the trace norm: $\|X\|_2 \le \|X\|_1$. -/
@[category API, AMS 46 47 81 94]
lemma hsNormSq_le_traceNorm_sq (X : Matrix n n ℂ) : hsNormSq X ≤ traceNorm X ^ 2 := by
  have hA := posSemidef_conjTranspose_mul_self X
  rw [traceNorm_eq_sum_sqrt_eigenvalues, hsNormSq_eq_sum_eigenvalues]
  calc ∑ i, hA.1.eigenvalues i = ∑ i, √(hA.1.eigenvalues i) ^ 2 := by
        simp only [Real.sq_sqrt (hA.eigenvalues_nonneg _)]
    _ ≤ (∑ i, √(hA.1.eigenvalues i)) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Real.sqrt_nonneg _

/-- The trace norm is dominated by the Hilbert–Schmidt norm up to the square root of the
dimension: $\|X\|_1 \le \sqrt{n} \, \|X\|_2$. This is Lemma 2 of [CL26]. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_sq_le_card_mul_hsNormSq (X : Matrix n n ℂ) :
    traceNorm X ^ 2 ≤ Fintype.card n * hsNormSq X := by
  have hA := posSemidef_conjTranspose_mul_self X
  rw [traceNorm_eq_sum_sqrt_eigenvalues, hsNormSq_eq_sum_eigenvalues]
  calc (∑ i, √(hA.1.eigenvalues i)) ^ 2
      ≤ Fintype.card n * ∑ i, √(hA.1.eigenvalues i) ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun i => √(hA.1.eigenvalues i))
    _ = Fintype.card n * ∑ i, hA.1.eigenvalues i := by
        simp only [Real.sq_sqrt (hA.eigenvalues_nonneg _)]

/-- The trace norm is definite: $\|X\|_1 = 0$ only for $X = 0$. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_eq_zero_iff {X : Matrix n n ℂ} : traceNorm X = 0 ↔ X = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ traceNorm_zero⟩
  have h1 := hsNormSq_le_traceNorm_sq X
  rw [h, zero_pow two_ne_zero] at h1
  have h2 : 0 ≤ (Xᴴ * X).trace := (posSemidef_conjTranspose_mul_self X).trace_nonneg
  refine trace_conjTranspose_mul_self_eq_zero_iff.mp (le_antisymm ?_ h2)
  rw [Complex.le_def] at h2 ⊢
  exact ⟨by simpa [hsNormSq] using h1, by simpa using h2.2.symm⟩

open scoped Matrix.Norms.Frobenius in
/-- Every linear map between matrix spaces is bounded with respect to the trace norm. -/
@[category API, AMS 46 47 81 94]
lemma exists_traceNorm_map_le (Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    ∃ C, 0 ≤ C ∧ ∀ X, traceNorm (Ψ X) ≤ C * traceNorm X := by
  have hF (Y : Matrix n n ℂ) : ‖Y‖ ^ 2 = hsNormSq Y := by
    rw [hsNormSq_eq_sum, frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
    simp
  obtain ⟨C, hC, h⟩ :=
    SemilinearMapClass.bound_of_continuous Ψ Ψ.continuous_of_finiteDimensional
  refine ⟨√(Fintype.card n) * C, by positivity, fun X => ?_⟩
  have h1 : traceNorm (Ψ X) ≤ √(Fintype.card n) * ‖Ψ X‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (Ψ X)), ← Real.sqrt_mul (Nat.cast_nonneg _), hF]
    exact Real.le_sqrt_of_sq_le (traceNorm_sq_le_card_mul_hsNormSq _)
  have h2 : ‖X‖ ≤ traceNorm X := by
    rw [← Real.sqrt_sq (traceNorm_nonneg X), ← Real.sqrt_sq (norm_nonneg X), hF]
    exact Real.sqrt_le_sqrt (hsNormSq_le_traceNorm_sq X)
  calc traceNorm (Ψ X) ≤ √(Fintype.card n) * ‖Ψ X‖ := h1
    _ ≤ √(Fintype.card n) * (C * traceNorm X) := by gcongr; exact (h X).trans (by gcongr)
    _ = √(Fintype.card n) * C * traceNorm X := by ring

end TraceNorm

/- ## Superoperators and tensoring with the identity -/

/-- A **superoperator** on a $d$-dimensional system: a linear map on the complex $d \times d$
matrices. -/
abbrev Superoperator (d : ℕ) := Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ

variable {d : ℕ}

/-- The superoperator $\Phi \otimes \mathrm{id}_m$ on
$\mathbb{C}^{d \times d} \otimes \mathbb{C}^{m \times m}$, the latter identified with the
matrices indexed by `Fin d × Fin m`. Writing
$X = \sum_{j_1, j_2} X_{j_1 j_2} \otimes |j_1\rangle\langle j_2|$ with blocks
$X_{j_1 j_2} \in \mathbb{C}^{d \times d}$, the map applies $\Phi$ to every block:
$$(\Phi \otimes \mathrm{id}_m)(X)_{(i_1, j_1), (i_2, j_2)} = \Phi(X_{j_1 j_2})_{i_1 i_2}.$$ -/
def tensorId (Φ : Superoperator d) (m : ℕ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ →ₗ[ℂ] Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ where
  toFun X := .of fun p q => Φ (X.submatrix (·, p.2) (·, q.2)) p.1 q.1
  map_add' X Y := by ext p q; simp [submatrix_add]
  map_smul' c X := by ext p q; simp [submatrix_smul]

/-- The entries of $(\Phi \otimes \mathrm{id}_m)(X)$. -/
@[simp, category API, AMS 46 47 81 94]
lemma tensorId_apply (Φ : Superoperator d) (m : ℕ)
    (X : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) (p q : Fin d × Fin m) :
    tensorId Φ m X p q = Φ (X.submatrix (·, p.2) (·, q.2)) p.1 q.1 := rfl

/-- $\mathrm{id} \otimes \mathrm{id}_m = \mathrm{id}$. -/
@[category API, AMS 46 47 81 94]
lemma tensorId_id (m : ℕ) : tensorId (LinearMap.id : Superoperator d) m = LinearMap.id := by
  ext X p q
  simp

/-- $(\Psi \circ \Phi) \otimes \mathrm{id}_m =
(\Psi \otimes \mathrm{id}_m) \circ (\Phi \otimes \mathrm{id}_m)$. -/
@[category API, AMS 46 47 81 94]
lemma tensorId_comp (Ψ Φ : Superoperator d) (m : ℕ) :
    tensorId (Ψ ∘ₗ Φ) m = tensorId Ψ m ∘ₗ tensorId Φ m := by
  ext X p q
  rfl

/-- $0 \otimes \mathrm{id}_m = 0$. -/
@[category API, AMS 46 47 81 94]
lemma tensorId_zero (m : ℕ) : tensorId (0 : Superoperator d) m = 0 := by
  ext X p q
  simp

/-- On elementary tensors, $(\Phi \otimes \mathrm{id}_m)(A \otimes B) = \Phi(A) \otimes B$.
Since elementary tensors span, this characterizes `tensorId Φ m` among linear maps. -/
@[category test, AMS 46 47 81 94]
theorem tensorId_kronecker (Φ : Superoperator d) (m : ℕ) (A : Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) : tensorId Φ m (A ⊗ₖ B) = Φ A ⊗ₖ B := by
  ext p q
  have h : (A ⊗ₖ B).submatrix (·, p.2) (·, q.2) = B p.2 q.2 • A := by
    ext a b
    simp [mul_comm]
  simp [h, mul_comm]

/- ## Quantum channels -/

/-- A superoperator $\Phi$ is **completely positive** if $\Phi \otimes \mathrm{id}_m$ maps
positive semidefinite matrices to positive semidefinite matrices for every $m$. -/
def IsCompletelyPositive (Φ : Superoperator d) : Prop :=
  ∀ (m : ℕ) (X : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ),
    X.PosSemidef → (tensorId Φ m X).PosSemidef

/-- A superoperator is **trace preserving** if $\operatorname{tr} \Phi(X) = \operatorname{tr} X$
for all $X$. -/
def IsTracePreserving (Φ : Superoperator d) : Prop :=
  ∀ X, (Φ X).trace = X.trace

/-- A **quantum channel** is a completely positive trace-preserving superoperator. -/
def IsQuantumChannel (Φ : Superoperator d) : Prop :=
  IsCompletelyPositive Φ ∧ IsTracePreserving Φ

/-- The identity is a quantum channel. -/
@[category test, AMS 46 47 81 94]
theorem isQuantumChannel_id : IsQuantumChannel (LinearMap.id : Superoperator d) :=
  ⟨fun m X hX => by simpa [tensorId_id] using hX, fun _ => rfl⟩

/-- The composition of two quantum channels is a quantum channel. -/
@[category API, AMS 46 47 81 94]
lemma isQuantumChannel_comp {Ψ Φ : Superoperator d} (hΨ : IsQuantumChannel Ψ)
    (hΦ : IsQuantumChannel Φ) : IsQuantumChannel (Ψ ∘ₗ Φ) :=
  ⟨fun m X hX => by simpa [tensorId_comp] using hΨ.1 m _ (hΦ.1 m X hX),
    fun X => by simp [hΨ.2 (Φ X), hΦ.2 X]⟩

/-- Conjugation $X \mapsto U X U^\dagger$ by a matrix $U$. For unitary $U$ this is the unitary
channel implemented by $U$. -/
def conjMap (U : Matrix (Fin d) (Fin d) ℂ) : Superoperator d where
  toFun X := U * X * Uᴴ
  map_add' X Y := by simp [mul_add, add_mul]
  map_smul' c X := by simp

/-- The value of the conjugation map. -/
@[simp, category API, AMS 46 47 81 94]
lemma conjMap_apply (U X : Matrix (Fin d) (Fin d) ℂ) : conjMap U X = U * X * Uᴴ := rfl

/-- Tensoring a conjugation with the identity is the conjugation by $U \otimes 1$. -/
@[category API, AMS 46 47 81 94]
lemma tensorId_conjMap (U : Matrix (Fin d) (Fin d) ℂ) (m : ℕ)
    (X : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) :
    tensorId (conjMap U) m X = (U ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * X * (U ⊗ₖ 1)ᴴ := by
  ext p q
  simp [mul_apply, Fintype.sum_prod_type, one_apply, apply_ite, ite_mul]

/-- Unitary conjugations are quantum channels. -/
@[category test, AMS 46 47 81 94]
theorem isQuantumChannel_conjMap {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) :
    IsQuantumChannel (conjMap U) :=
  ⟨fun m X hX => by rw [tensorId_conjMap]; exact hX.mul_mul_conjTranspose_same _,
    fun X => by rw [conjMap_apply, trace_mul_cycle, hU, one_mul]⟩

/- ## The transposition map -/

/-- The **transposition map** $\Theta(X) = X^{\mathsf T}$ with respect to the standard basis. -/
def transposeMap (d : ℕ) : Superoperator d :=
  (Matrix.transposeLinearEquiv (Fin d) (Fin d) ℂ ℂ).toLinearMap

/-- The value of the transposition map. -/
@[simp, category API, AMS 46 47 81 94]
lemma transposeMap_apply (X : Matrix (Fin d) (Fin d) ℂ) : transposeMap d X = Xᵀ := rfl

/-- $\Theta \otimes \mathrm{id}_m$ is the partial transposition on the first tensor factor. -/
@[category API, AMS 46 47 81 94]
lemma tensorId_transposeMap_apply (m : ℕ) (X : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ)
    (p q : Fin d × Fin m) : tensorId (transposeMap d) m X p q = X (q.1, p.2) (p.1, q.2) := rfl

/-- The transposition map is trace preserving. -/
@[category test, AMS 46 47 81 94]
theorem isTracePreserving_transposeMap : IsTracePreserving (transposeMap d) :=
  fun X => trace_transpose X

/-- The transposition map is positive: it maps positive semidefinite matrices to positive
semidefinite matrices. -/
@[category test, AMS 46 47 81 94]
theorem posSemidef_transposeMap {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) :
    (transposeMap d X).PosSemidef :=
  hX.transpose

/-- Partial transposition preserves the Hilbert–Schmidt norm, because it only permutes the
entries. This is Lemma 3 of [CL26]. -/
@[category API, AMS 46 47 81 94]
lemma hsNormSq_tensorId_transposeMap (m : ℕ) (X : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) :
    hsNormSq (tensorId (transposeMap d) m X) = hsNormSq X := by
  simp only [hsNormSq_eq_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ⟨fun pq => ((pq.2.1, pq.1.2), (pq.1.1, pq.2.2)),
    fun pq => ((pq.2.1, pq.1.2), (pq.1.1, pq.2.2)), fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => rfl

/-- The unnormalized maximally entangled operator $|\Omega\rangle\langle\Omega|$ on
$\mathbb{C}^d \otimes \mathbb{C}^d$, where $|\Omega\rangle = \sum_i |i\rangle \otimes |i\rangle$. -/
def maxEntangled (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  vecMulVec (fun p => if p.1 = p.2 then 1 else 0) (star fun p => if p.1 = p.2 then 1 else 0)

/-- The swap operator $F$ on $\mathbb{C}^d \otimes \mathbb{C}^d$, with
$F (x \otimes y) = y \otimes x$. -/
def swapMatrix (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin d) (Fin d))

/-- The maximally entangled operator is positive semidefinite. -/
@[category API, AMS 46 47 81 94]
lemma posSemidef_maxEntangled : (maxEntangled d).PosSemidef :=
  posSemidef_vecMulVec_self_star _

/-- $\| |\Omega\rangle\langle\Omega| \|_1 = d$. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_maxEntangled : traceNorm (maxEntangled d) = d := by
  rw [traceNorm_posSemidef posSemidef_maxEntangled]
  simp [maxEntangled, trace, vecMulVec_apply, Fintype.sum_prod_type]

/-- The entries of the swap operator. -/
@[category API, AMS 46 47 81 94]
lemma swapMatrix_apply (p q : Fin d × Fin d) :
    swapMatrix d p q = if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0 := by
  simp [swapMatrix, PEquiv.toMatrix_apply, Prod.ext_iff, and_comm]

/-- The partial transpose of the maximally entangled operator is the swap operator:
$(\Theta \otimes \mathrm{id})(|\Omega\rangle\langle\Omega|) = F$. -/
@[category API, AMS 46 47 81 94]
lemma tensorId_transposeMap_maxEntangled :
    tensorId (transposeMap d) d (maxEntangled d) = swapMatrix d := by
  ext p q
  simp [swapMatrix_apply, maxEntangled, vecMulVec_apply, eq_comm, ite_and]

/-- The swap operator is unitary, so $\|F\|_1 = d^2$. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_swapMatrix : traceNorm (swapMatrix d) = d * d := by
  rw [traceNorm_of_conjTranspose_mul_self_eq_one]
  · simp
  · rw [swapMatrix, conjTranspose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

/-- $\operatorname{tr} F = d$. -/
@[category API, AMS 46 47 81 94]
lemma trace_swapMatrix : (swapMatrix d).trace = d := by
  have h (i j : Fin d) : swapMatrix d (i, j) (i, j) = if i = j then 1 else 0 := by
    simp [swapMatrix_apply, eq_comm]
  simp only [trace, diag_apply, Fintype.sum_prod_type, h, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  simp

/-- The transposition map is not completely positive in dimension $d \ge 2$: it maps the
positive semidefinite operator $|\Omega\rangle\langle\Omega|$ to the swap operator, which is
not positive semidefinite, since its trace is $d$ but its trace norm is $d^2$. In particular,
transposition is not a quantum channel. -/
@[category test, AMS 46 47 81 94]
theorem not_isCompletelyPositive_transposeMap (hd : 2 ≤ d) :
    ¬ IsCompletelyPositive (transposeMap d) := by
  intro h
  have key := traceNorm_posSemidef (h d _ posSemidef_maxEntangled)
  rw [tensorId_transposeMap_maxEntangled, traceNorm_swapMatrix, trace_swapMatrix] at key
  have h1 : (d : ℝ) * d = d := by simpa using key
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

/- ## The diamond norm -/

/-- The **diamond norm** (completely bounded trace norm) of a superoperator $\Phi$ on
$\mathbb{C}^{d \times d}$:
$$\|\Phi\|_\diamond = \sup \{ \|(\Phi \otimes \mathrm{id}_d)(X)\|_1 : \|X\|_1 \le 1 \},$$
where $X$ ranges over the matrices on $\mathbb{C}^d \otimes \mathbb{C}^d$.

The ancilla has the same dimension $d$ as the system, as in [Wat18, Definition 3.43]. This
loses nothing: an ancilla of any other dimension $m$ gives at most $\|\Phi\|_\diamond$, see
`diamondNorm_stabilization`. The set whose supremum is taken is nonempty and bounded above,
see `bddAbove_diamondNorm`, so `sSup` is a genuine supremum.

Some authors, including [CL26], take the supremum only over density matrices $X$. For
Hermiticity-preserving $\Phi$ this gives the same value [Wat18, Theorem 3.51], and all
superoperators in the problem, namely $\Theta$, $\mathrm{id} - T$ and
$\Theta \circ (\mathrm{id} - T)$, are Hermiticity preserving. -/
def diamondNorm (Φ : Superoperator d) : ℝ :=
  sSup {r : ℝ | ∃ X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
    traceNorm X ≤ 1 ∧ traceNorm (tensorId Φ d X) = r}

/-- The diamond norm is nonnegative. -/
@[category API, AMS 46 47 81 94]
lemma diamondNorm_nonneg (Φ : Superoperator d) : 0 ≤ diamondNorm Φ :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ traceNorm_nonneg _

/-- The set whose supremum defines the diamond norm is bounded above. -/
@[category API, AMS 46 47 81 94]
lemma bddAbove_diamondNorm (Φ : Superoperator d) :
    BddAbove {r : ℝ | ∃ X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      traceNorm X ≤ 1 ∧ traceNorm (tensorId Φ d X) = r} := by
  obtain ⟨C, hC, h⟩ := exists_traceNorm_map_le (tensorId Φ d)
  refine ⟨C, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact (h X).trans (mul_le_of_le_one_right hC hX)

/-- The defining property of the diamond norm:
$\|(\Phi \otimes \mathrm{id}_d)(X)\|_1 \le \|\Phi\|_\diamond \, \|X\|_1$. -/
@[category API, AMS 46 47 81 94]
lemma traceNorm_tensorId_le (Φ : Superoperator d)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    traceNorm (tensorId Φ d X) ≤ diamondNorm Φ * traceNorm X := by
  obtain h | h := (traceNorm_nonneg X).eq_or_lt
  · simp [traceNorm_eq_zero_iff.mp h.symm]
  · have key := le_csSup (bddAbove_diamondNorm Φ)
      ⟨((traceNorm X)⁻¹ : ℂ) • X, by simp [traceNorm_smul, abs_of_pos h, h.ne'], rfl⟩
    rw [map_smul, traceNorm_smul] at key
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h] at key
    rwa [inv_mul_le_iff₀ h, mul_comm] at key

/-- A uniform bound on the unit ball of the trace norm bounds the diamond norm. -/
@[category API, AMS 46 47 81 94]
lemma diamondNorm_le_of_forall {Φ : Superoperator d} {c : ℝ}
    (h : ∀ X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ, traceNorm X ≤ 1 →
      traceNorm (tensorId Φ d X) ≤ c) : diamondNorm Φ ≤ c :=
  csSup_le ⟨_, 0, by simp, rfl⟩ fun _ ⟨X, hX, hr⟩ => hr ▸ h X hX

/-- The diamond norm of the zero map is $0$. -/
@[category test, AMS 46 47 81 94]
theorem diamondNorm_zero : diamondNorm (0 : Superoperator d) = 0 :=
  le_antisymm (diamondNorm_le_of_forall fun X _ => by simp [tensorId_zero]) (diamondNorm_nonneg 0)

/-- The diamond norm of the identity is $1$ in every positive dimension. -/
@[category test, AMS 46 47 81 94]
theorem diamondNorm_id [NeZero d] : diamondNorm (LinearMap.id : Superoperator d) = 1 := by
  have h : traceNorm (((Fintype.card (Fin d × Fin d) : ℂ)⁻¹) •
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) = 1 := by
    rw [traceNorm_smul, traceNorm_of_conjTranspose_mul_self_eq_one (by simp), norm_inv,
      Complex.norm_natCast, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  refine IsGreatest.csSup_eq ⟨⟨_, h.le, by rw [tensorId_id]; exact h⟩, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  simpa [tensorId_id] using hX

/-- **Ordinary submultiplicativity** of the diamond norm:
$\|\Phi \circ \Psi\|_\diamond \le \|\Phi\|_\diamond \, \|\Psi\|_\diamond$. -/
@[category API, AMS 46 47 81 94]
lemma diamondNorm_comp_le (Φ Ψ : Superoperator d) :
    diamondNorm (Φ ∘ₗ Ψ) ≤ diamondNorm Φ * diamondNorm Ψ := by
  refine diamondNorm_le_of_forall fun X hX => ?_
  calc traceNorm (tensorId (Φ ∘ₗ Ψ) d X) = traceNorm (tensorId Φ d (tensorId Ψ d X)) := by
        rw [tensorId_comp, LinearMap.comp_apply]
    _ ≤ diamondNorm Φ * traceNorm (tensorId Ψ d X) := traceNorm_tensorId_le Φ _
    _ ≤ diamondNorm Φ * (diamondNorm Ψ * 1) := by
        gcongr
        · exact diamondNorm_nonneg Φ
        · exact (traceNorm_tensorId_le Ψ X).trans (by gcongr; exact diamondNorm_nonneg Ψ)
    _ = diamondNorm Φ * diamondNorm Ψ := by ring

/-- **Stabilization** of the diamond norm [Wat18, Theorem 3.46]: an ancilla of arbitrary
dimension $m$ does not give more than the ancilla of dimension $d$ used in the definition, i.e.
$\|(\Phi \otimes \mathrm{id}_m)(X)\|_1 \le \|\Phi\|_\diamond \, \|X\|_1$ for all $m$. Hence
`diamondNorm Φ` is the supremum of $\|(\Phi \otimes \mathrm{id}_m)(X)\|_1$ over all $m$ and all
$X$ with $\|X\|_1 \le 1$. The case $m = d$ is `traceNorm_tensorId_le`. -/
@[category textbook, AMS 46 47 81 94]
theorem diamondNorm_stabilization (Φ : Superoperator d) (m : ℕ)
    (X : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) :
    traceNorm (tensorId Φ m X) ≤ diamondNorm Φ * traceNorm X := by
  sorry

/-- $\|\Theta\|_\diamond \le d$, by comparing the trace norm with the Hilbert–Schmidt norm,
which partial transposition preserves. -/
@[category API, AMS 46 47 81 94]
lemma diamondNorm_transposeMap_le : diamondNorm (transposeMap d) ≤ d := by
  refine diamondNorm_le_of_forall fun X hX => ?_
  refine (sq_le_sq₀ (traceNorm_nonneg _) (Nat.cast_nonneg d)).mp ?_
  calc traceNorm (tensorId (transposeMap d) d X) ^ 2
      ≤ Fintype.card (Fin d × Fin d) * hsNormSq X := by
        rw [← hsNormSq_tensorId_transposeMap]
        exact traceNorm_sq_le_card_mul_hsNormSq _
    _ ≤ (d : ℝ) ^ 2 * 1 := by
        rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, ← sq]
        gcongr
        exact (hsNormSq_le_traceNorm_sq X).trans (pow_le_one₀ (traceNorm_nonneg X) hX)
    _ = (d : ℝ) ^ 2 := mul_one _

/-- $d \le \|\Theta\|_\diamond$: the maximally entangled operator has trace norm $d$ and its
partial transpose, the swap operator, has trace norm $d^2$. -/
@[category API, AMS 46 47 81 94]
lemma le_diamondNorm_transposeMap : (d : ℝ) ≤ diamondNorm (transposeMap d) := by
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · simpa using diamondNorm_nonneg (transposeMap 0)
  · have h := traceNorm_tensorId_le (transposeMap d) (maxEntangled d)
    rw [tensorId_transposeMap_maxEntangled, traceNorm_swapMatrix, traceNorm_maxEntangled] at h
    exact le_of_mul_le_mul_right h (Nat.cast_pos.mpr hd)

/-- The diamond norm of the transposition map is the dimension: $\|\Theta\|_\diamond = d$.
This is the fact quoted in the statement of the problem; see [Tom83] and
[Wat18, Example 3.42]. -/
@[category textbook, AMS 46 47 81 94]
theorem diamondNorm_transposeMap : diamondNorm (transposeMap d) = d :=
  le_antisymm diamondNorm_transposeMap_le le_diamondNorm_transposeMap

/- ## The problem -/

/-- `IsSubmultiplicativityConstant α` states that the strengthened submultiplicativity
inequality
$$\|\Theta \circ (\mathrm{id} - T)\|_\diamond \le
  \alpha \, \|\Theta\|_\diamond \, \|\mathrm{id} - T\|_\diamond$$
holds with the constant $\alpha$ for all quantum channels $T$ on $\mathbb{C}^{d \times d}$ and
all dimensions $d$. -/
def IsSubmultiplicativityConstant (α : ℝ) : Prop :=
  ∀ (d : ℕ) (T : Superoperator d), IsQuantumChannel T →
    diamondNorm (transposeMap d ∘ₗ (LinearMap.id - T)) ≤
      α * diamondNorm (transposeMap d) * diamondNorm (LinearMap.id - T)

/-- Since $\|\Theta\|_\diamond = d$, the inequality reads
$\|\Theta \circ (\mathrm{id} - T)\|_\diamond \le \alpha \, d \, \|\mathrm{id} - T\|_\diamond$. -/
@[category API, AMS 46 47 81 94]
lemma isSubmultiplicativityConstant_iff {α : ℝ} :
    IsSubmultiplicativityConstant α ↔ ∀ (d : ℕ) (T : Superoperator d), IsQuantumChannel T →
      diamondNorm (transposeMap d ∘ₗ (LinearMap.id - T)) ≤
        α * d * diamondNorm (LinearMap.id - T) := by
  simp only [IsSubmultiplicativityConstant, diamondNorm_transposeMap]

/-- The admissible constants are upward closed. -/
@[category API, AMS 46 47 81 94]
lemma IsSubmultiplicativityConstant.mono {α β : ℝ} (hα : IsSubmultiplicativityConstant α)
    (hαβ : α ≤ β) : IsSubmultiplicativityConstant β := fun d T hT =>
  (hα d T hT).trans (by gcongr <;> exact diamondNorm_nonneg _)

/-- Ordinary submultiplicativity is the case $\alpha = 1$. -/
@[category test, AMS 46 47 81 94]
theorem isSubmultiplicativityConstant_one : IsSubmultiplicativityConstant 1 := fun d T _ => by
  simpa using diamondNorm_comp_le (transposeMap d) (LinearMap.id - T)

/-- Admissible constants are positive, so the inequality of the problem is not vacuous. The
witness is the qubit channel $T(\rho) = Z \rho Z$ with $Z = \operatorname{diag}(1, -1)$, for
which $\Theta \circ (\mathrm{id} - T)$ does not vanish. -/
@[category test, AMS 46 47 81 94]
theorem IsSubmultiplicativityConstant.pos {α : ℝ} (hα : IsSubmultiplicativityConstant α) :
    0 < α := by
  let U : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, -1]
  have hU : Uᴴ * U = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [U, diagonal_conjTranspose]
  have key := hα 2 (conjMap U) (isQuantumChannel_conjMap hU)
  set Ξ : Superoperator 2 := transposeMap 2 ∘ₗ (LinearMap.id - conjMap U)
  set X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.single 0 1 1 ⊗ₖ 1 with hX
  have hne : tensorId Ξ 2 X ≠ 0 := by
    rw [hX, tensorId_kronecker]
    intro h
    have := congrFun (congrFun h (1, 0)) (0, 0)
    simp [Ξ, U, diagonal_conjTranspose] at this
  have hpos : 0 < traceNorm (tensorId Ξ 2 X) :=
    (traceNorm_nonneg _).lt_of_ne' (mt traceNorm_eq_zero_iff.mp hne)
  have hle := traceNorm_tensorId_le Ξ X
  by_contra hα'
  have hL : diamondNorm Ξ ≤ 0 := key.trans (mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hα') (diamondNorm_nonneg _)) (diamondNorm_nonneg _))
  rw [le_antisymm hL (diamondNorm_nonneg _), zero_mul] at hle
  exact hpos.not_ge hle

/-- There is a least admissible constant: the optimal constant $\alpha_*$ exists. -/
@[category test, AMS 46 47 81 94]
theorem exists_isLeast_isSubmultiplicativityConstant :
    ∃ a, IsLeast {α : ℝ | IsSubmultiplicativityConstant α} a := by
  have hbdd : BddBelow {α : ℝ | IsSubmultiplicativityConstant α} := ⟨0, fun α hα => hα.pos.le⟩
  refine ⟨sInf {α : ℝ | IsSubmultiplicativityConstant α}, fun d T hT => ?_,
    fun α hα => csInf_le hbdd hα⟩
  set c := diamondNorm (transposeMap d) * diamondNorm (LinearMap.id - T) with hc
  have hc0 : 0 ≤ c := mul_nonneg (diamondNorm_nonneg _) (diamondNorm_nonneg _)
  have h (α : ℝ) (hα : IsSubmultiplicativityConstant α) :
      diamondNorm (transposeMap d ∘ₗ (LinearMap.id - T)) ≤ α * c := by
    simpa [hc, mul_assoc] using hα d T hT
  rw [mul_assoc, ← hc]
  obtain hc' | hc' := hc0.eq_or_lt
  · simpa [← hc'] using h 1 isSubmultiplicativityConstant_one
  · rw [← div_le_iff₀ hc']
    exact le_csInf ⟨1, isSubmultiplicativityConstant_one⟩ fun α hα => (div_le_iff₀ hc').mpr (h α hα)

/-- Cha and Lee [CL26, Theorem 1]: for every quantum channel $T$ on $\mathbb{C}^{d \times d}$,
$$\|\Theta \circ (\mathrm{id} - T)\|_\diamond \le
  \frac{1}{\sqrt 2} \, \|\Theta\|_\diamond \, \|\mathrm{id} - T\|_\diamond .$$
This answers Open Quantum Problem 37 with the explicit constant $\alpha = 1/\sqrt 2$. -/
@[category research solved, AMS 46 47 81 94]
theorem stronger_submultiplicativity_diamond_norm.variants.inv_sqrt_two :
    IsSubmultiplicativityConstant (1 / √2) := by
  sorry

/-- Cha and Lee [CL26, Remark 1]: the bound with $\alpha = 1/\sqrt 2$ holds for every
Hermiticity-preserving and trace-annihilating superoperator $\Psi$ in place of
$\mathrm{id} - T$, i.e.
$\|\Theta \circ \Psi\|_\diamond \le \frac{1}{\sqrt 2} \, \|\Theta\|_\diamond \, \|\Psi\|_\diamond$.
If $T$ is a quantum channel then $\Psi = \mathrm{id} - T$ is of this form. -/
@[category research solved, AMS 46 47 81 94]
theorem stronger_submultiplicativity_diamond_norm.variants.hermitian_preserving (d : ℕ)
    (Ψ : Superoperator d) (hherm : ∀ X, Ψ Xᴴ = (Ψ X)ᴴ) (htr : ∀ X, (Ψ X).trace = 0) :
    diamondNorm (transposeMap d ∘ₗ Ψ) ≤
      1 / √2 * diamondNorm (transposeMap d) * diamondNorm Ψ := by
  sorry

/-- **Open Quantum Problem 37.** Does there exist an absolute constant $\alpha < 1$ such that
the submultiplicativity statement
$$\|\Theta \circ (\mathrm{id} - T)\|_\diamond \le
  \alpha \, \|\Theta\|_\diamond \, \|\mathrm{id} - T\|_\diamond$$
holds for all quantum channels $T$ over any finite-dimensional Hilbert space? Here $\Theta$
denotes the transposition map, so $\|\Theta\|_\diamond$ equals the Hilbert space dimension.

The answer is yes: Cha and Lee [CL26] proved that $\alpha = 1/\sqrt 2$ works, and the problem
is listed as solved on the Open Quantum Problems site. -/
@[category research solved, question, AMS 46 47 81 94]
theorem stronger_submultiplicativity_diamond_norm :
    ∃ α < 1, IsSubmultiplicativityConstant α := by
  refine ⟨1 / √2, ?_, stronger_submultiplicativity_diamond_norm.variants.inv_sqrt_two⟩
  rw [div_lt_one (by positivity), Real.lt_sqrt (by norm_num)]
  norm_num

/-- No absolute constant below $2/\pi \approx 0.6366$ is admissible. For $d \ge 2$ let $T_d$ be
the unitary channel $T_d(\rho) = U_d \rho U_d^\dagger$ with
$U_d = \operatorname{diag}(1, \omega, \dots, \omega^{d-1})$ and $\omega = e^{2 \pi i / d}$. Then
$\|\mathrm{id} - T_d\|_\diamond = 2$ and
$\|\Theta \circ (\mathrm{id} - T_d)\|_\diamond \ge 2 \cot(\pi / (2 d))$, so every admissible
constant satisfies $\alpha \ge \cot(\pi / (2 d)) / d$, which tends to $2/\pi$ as
$d \to \infty$. The Open Quantum Problems page attributes the bound $\alpha > 0.63$ to
Fischer [Fis16]; a self-contained proof is given in [CL26, Appendix A]. -/
@[category research solved, AMS 46 47 81 94]
theorem stronger_submultiplicativity_diamond_norm.variants.two_div_pi_le {α : ℝ}
    (hα : IsSubmultiplicativityConstant α) : 2 / Real.pi ≤ α := by
  sorry

/-- For qubit channels $T$ one has
$\|\Theta \circ (\mathrm{id} - T)\|_\diamond = \|\mathrm{id} - T\|_\diamond$. Since
$\|\Theta\|_\diamond = 2$ in dimension $2$, the inequality of the problem holds with
$\alpha = 1/2$ and with equality, so $1/2$ is the exact best constant for qubits. -/
@[category research solved, AMS 46 47 81 94]
theorem stronger_submultiplicativity_diamond_norm.variants.qubit (T : Superoperator 2)
    (hT : IsQuantumChannel T) :
    diamondNorm (transposeMap 2 ∘ₗ (LinearMap.id - T)) = diamondNorm (LinearMap.id - T) := by
  sorry

/-- Is there an admissible absolute constant strictly below $1/\sqrt 2$? This is the second
part of [CL26, Problem 1]. Section VI of [CL26] shows that the inequality with
$\alpha = 1/\sqrt 2$ is strict for every channel $T \ne \mathrm{id}$ in every fixed dimension.
This does not decide the question, because the supremum of the ratio of the two sides over all
channels and all dimensions may still be $1/\sqrt 2$. -/
@[category research open, question, AMS 46 47 81 94]
theorem stronger_submultiplicativity_diamond_norm.variants.lt_inv_sqrt_two :
    ∃ α < 1 / √2, IsSubmultiplicativityConstant α := by
  sorry

/-- The optimal absolute constant $\alpha_*$ of Open Quantum Problem 37. -/
def optimal_submultiplicativity_constant.answer : ℝ := sorry

/-- What is the optimal absolute constant $\alpha_*$ in the strengthened submultiplicativity
inequality, i.e. the least $\alpha$ for which it holds for all quantum channels in all
dimensions? This is [CL26, Problem 1]. The set of admissible constants is upward closed
(`IsSubmultiplicativityConstant.mono`) and has a least element
(`exists_isLeast_isSubmultiplicativityConstant`), so it is a ray $[\alpha_*, \infty)$. At
present $2/\pi \le \alpha_* \le 1/\sqrt 2$, see
`optimal_submultiplicativity_constant.variants.bounds`. -/
@[category research open, question value, AMS 46 47 81 94]
theorem optimal_submultiplicativity_constant :
    IsLeast {α : ℝ | IsSubmultiplicativityConstant α}
      optimal_submultiplicativity_constant.answer := by
  sorry

/-- The known bounds $2/\pi \le \alpha_* \le 1/\sqrt 2$ on the optimal constant. -/
@[category research solved, AMS 46 47 81 94]
theorem optimal_submultiplicativity_constant.variants.bounds {a : ℝ}
    (ha : IsLeast {α : ℝ | IsSubmultiplicativityConstant α} a) :
    2 / Real.pi ≤ a ∧ a ≤ 1 / √2 :=
  ⟨stronger_submultiplicativity_diamond_norm.variants.two_div_pi_le ha.1,
    ha.2 stronger_submultiplicativity_diamond_norm.variants.inv_sqrt_two⟩

end OpenQuantumProblem37
