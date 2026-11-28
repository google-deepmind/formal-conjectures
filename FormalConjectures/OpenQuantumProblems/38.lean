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
# Open Quantum Problem 38: The PPT-squared conjecture

Two sources prepare independent states on $AB$ and $CD$, each positive under partial transpose
(PPT). An outcome of a joint measurement on $BC$ leaves a conditional state on $AD$. The
conjecture asserted that this state is always separable. The corresponding map conjecture
asserted that the composition of any two PPT maps is entanglement breaking.

Both unrestricted claims are false. OpenAI (2026), Theorems 1.2 and 1.3, constructs a pair
of PPT maps on $M_{10}(\mathbb C)$ and a single trace-preserving PPT map on $M_{21}(\mathbb C)$
whose respective composition and square are not entanglement breaking. In the state picture,
the two normalized Choi matrices serve as sources and projection onto a maximally entangled
vector on the middle systems produces the normalized Choi matrix of the composition.
The two-map claim holds in equal dimensions two and three. Dimension four remains open.

## References

- [Open Quantum Problem 38](https://oqp.iqoqi.oeaw.ac.at/the-ppt-squared-conjecture)
  and [Formal Conjectures issue #3455](https://github.com/google-deepmind/formal-conjectures/issues/3455).
- BIRS, *Operator Structures in Quantum Information Theory*, workshop report 12w5084 (2012),
  [open problems session](https://www.birs.ca/workshops/2012/12w5084/report12w5084.pdf).
- M. Christandl, A. Müller-Hermes and M. M. Wolf, *When do composed maps become entanglement
  breaking?* (2019), [arXiv:1807.01266](https://arxiv.org/abs/1807.01266).
- M. Kennedy, N. A. Manor and V. I. Paulsen, *Composition of PPT maps* (2018),
  [arXiv:1710.08475](https://arxiv.org/abs/1710.08475).
- L. Chen, Y. Yang and W. Tang, *The positive partial transpose conjecture for $n=3$* (2019),
  [arXiv:1807.03636](https://arxiv.org/abs/1807.03636).
- S. Singh and I. Nechita, *The PPT² conjecture holds for all Choi-type maps* (2022),
  [arXiv:2011.03809](https://arxiv.org/abs/2011.03809).
- OpenAI, *Entanglement with zero distillable secret key in local dimension ten* (2026),
  [paper and scope of the Lean proofs](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/272.md).
- T. S. Tomar, *The PPT-squared conjecture holds for spin-factor maps* (2026),
  [Introduction](https://hexagonmath.org/pdf/2611.00386v1), for the status of dimension four.
-/

@[expose] public section

open Matrix
open scoped Kronecker ComplexOrder

namespace OpenQuantumProblem38

noncomputable section

variable {A B C D : Type*}

/-- A square matrix in the computational basis of a system indexed by $I$. -/
abbrev Operator (I : Type*) := Matrix I I ℂ

/-- A density matrix is positive semidefinite and has trace one. -/
def IsDensityMatrix [Fintype A] (ρ : Operator A) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Transpose the second tensor factor in its computational basis. -/
def partialTransposeRight (X : Operator (A × B)) : Operator (A × B) :=
  fun i j ↦ X (i.1, j.2) (j.1, i.2)

/-- A bipartite operator and its right partial transpose are both positive semidefinite. -/
def IsPPT (X : Operator (A × B)) : Prop :=
  X.PosSemidef ∧ (partialTransposeRight X).PosSemidef

/-- A separable state is a finite convex combination of product density matrices. -/
def IsSeparable [Fintype A] [Fintype B] (ρ : Operator (A × B)) : Prop :=
  ∃ (k : ℕ) (p : Fin k → ℝ) (X : Fin k → Operator A) (Y : Fin k → Operator B),
    (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
    (∀ i, IsDensityMatrix (X i)) ∧ (∀ i, IsDensityMatrix (Y i)) ∧
    ρ = ∑ i, (p i : ℂ) • (X i ⊗ₖ Y i)

@[category API, AMS 15 81]
theorem partialTransposeRight_involutive : Function.Involutive (@partialTransposeRight A B) :=
  fun _ ↦ rfl

@[category test, AMS 15 81]
theorem isSeparable_kronecker [Fintype A] [Fintype B] {X : Operator A} {Y : Operator B}
    (hX : IsDensityMatrix X) (hY : IsDensityMatrix Y) : IsSeparable (X ⊗ₖ Y) := by
  exact ⟨1, fun _ ↦ 1, fun _ ↦ X, fun _ ↦ Y, by simp, by simp, fun _ ↦ hX, fun _ ↦ hY, by simp⟩

@[category API, AMS 15 81]
theorem isPPT_of_isSeparable [Fintype A] [Fintype B] {ρ : Operator (A × B)}
    (h : IsSeparable ρ) : IsPPT ρ := by
  obtain ⟨k, p, X, Y, hp, _, hX, hY, rfl⟩ := h
  constructor
  · exact posSemidef_sum _ fun i _ ↦
      ((hX i).1.kronecker (hY i).1).smul (Complex.zero_le_real.mpr (hp i))
  · have ht : partialTransposeRight (∑ i, (p i : ℂ) • (X i ⊗ₖ Y i)) =
        ∑ i, (p i : ℂ) • (X i ⊗ₖ (Y i)ᵀ) := by
      ext i j
      simp [partialTransposeRight, Matrix.sum_apply]
    rw [ht]
    exact posSemidef_sum _ fun i _ ↦
      ((hX i).1.kronecker (hY i).1.transpose).smul (Complex.zero_le_real.mpr (hp i))

@[category API, AMS 15 81]
theorem isDensityMatrix_of_isSeparable [Fintype A] [Fintype B] {ρ : Operator (A × B)}
    (h : IsSeparable ρ) : IsDensityMatrix ρ := by
  refine ⟨(isPPT_of_isSeparable h).1, ?_⟩
  obtain ⟨k, p, X, Y, _, hsum, hX, hY, rfl⟩ := h
  simpa [trace_sum, trace_smul, trace_kronecker, (hX _).2, (hY _).2] using
    congrArg Complex.ofReal hsum

/-- The operator $|\Omega\rangle\langle\Omega|$ for $|\Omega\rangle=\sum_i |ii\rangle$. -/
def maximallyEntangledOperator (B : Type*) [DecidableEq B] : Operator (B × B) :=
  let v : B × B → ℂ := fun i ↦ if i.1 = i.2 then 1 else 0
  vecMulVec v (star v)

/-- The normalized projector onto $(|00\rangle+|11\rangle)/\sqrt 2$. -/
def bellState : Operator (Fin 2 × Fin 2) :=
  (2 : ℂ)⁻¹ • maximallyEntangledOperator (Fin 2)

@[category test, AMS 15 81]
theorem isDensityMatrix_bellState : IsDensityMatrix bellState := by
  constructor
  · exact (posSemidef_vecMulVec_self_star _).smul
      (by norm_num [Complex.nonneg_iff] : 0 ≤ (2 : ℂ)⁻¹)
  · norm_num [bellState, maximallyEntangledOperator, trace, diag, Fintype.sum_prod_type,
      Fin.sum_univ_two, vecMulVec]

/-- The antisymmetric vector $|01\rangle-|10\rangle$ detects the negative partial transpose. -/
@[category test, AMS 15 81]
theorem not_isPPT_bellState : ¬ IsPPT bellState := by
  intro h
  let v : Fin 2 × Fin 2 → ℂ := fun i ↦ if i = (0, 1) then 1 else if i = (1, 0) then -1 else 0
  have hv := h.2.re_dotProduct_nonneg v
  norm_num [bellState, maximallyEntangledOperator, partialTransposeRight, dotProduct, mulVec,
    Fintype.sum_prod_type, Fin.sum_univ_two, vecMulVec, v] at hv

section Swapping

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

/-- The partial trace over $BC$ in the ordering $(AD)(BC)$. -/
def partialTraceMiddle (X : Operator ((A × D) × (B × C))) : Operator (A × D) :=
  fun i j ↦ ∑ t, X (i, t) (j, t)

/-- Write $\rho_{AB}\otimes\tau_{CD}$ in the order $(AD)(BC)$. -/
def jointState (ρ : Operator (A × B)) (τ : Operator (C × D)) : Operator ((A × D) × (B × C)) :=
  let f := fun (i : (A × D) × (B × C)) ↦ ((i.1.1, i.2.1), (i.2.2, i.1.2))
  (ρ ⊗ₖ τ).submatrix f f

variable [DecidableEq A] [DecidableEq D]

/-- The unnormalized output $\operatorname{Tr}_{BC}[(\rho_{AB}\otimes\tau_{CD})
(I_A\otimes M_{BC}\otimes I_D)]$. -/
def swappedUnnormalized (ρ : Operator (A × B)) (τ : Operator (C × D)) (M : Operator (B × C)) :
    Operator (A × D) :=
  partialTraceMiddle (jointState ρ τ * ((1 : Operator (A × D)) ⊗ₖ M))

/-- The outcome weight. For a measurement effect $0\leq M\leq I$ this is a probability.
Scaling a positive $M$ to an effect does not change the normalized output. -/
def successWeight (ρ : Operator (A × B)) (τ : Operator (C × D)) (M : Operator (B × C)) : ℂ :=
  (swappedUnnormalized ρ τ M).trace

/-- Condition on the middle measurement outcome when its weight is nonzero. -/
def swappedState (ρ : Operator (A × B)) (τ : Operator (C × D)) (M : Operator (B × C)) :
    Operator (A × D) :=
  (successWeight ρ τ M)⁻¹ • swappedUnnormalized ρ τ M

variable (ρ : Operator (A × B)) (τ : Operator (C × D)) (M : Operator (B × C))

@[category API, AMS 15 81]
theorem successWeight_eq_trace : successWeight ρ τ M =
    (jointState ρ τ * ((1 : Operator (A × D)) ⊗ₖ M)).trace := by
  simp [successWeight, swappedUnnormalized, partialTraceMiddle, trace, diag, Fintype.sum_prod_type]

open scoped MatrixOrder in
/-- The complex trace defining the success weight is real and nonnegative. -/
@[category API, AMS 15 81]
theorem successWeight_nonneg (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef) (hM : M.PosSemidef) :
    0 ≤ (successWeight ρ τ M).re ∧ (successWeight ρ τ M).im = 0 := by
  classical
  rw [successWeight_eq_trace]
  have hJ : (jointState ρ τ).PosSemidef := (hρ.kronecker hτ).submatrix _
  have hE := (PosSemidef.one (n := A × D) (R := ℂ)).kronecker hM
  obtain ⟨K, hK⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  rw [hK, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact (Complex.nonneg_iff.mp (hJ.mul_mul_conjTranspose_same K).trace_nonneg).imp_right Eq.symm

@[category API, AMS 15 81]
theorem trace_swappedState (hp : successWeight ρ τ M ≠ 0) : (swappedState ρ τ M).trace = 1 := by
  rw [swappedState, trace_smul]
  exact inv_mul_cancel₀ hp

/-- Contract both middle row indices against the corresponding column indices of $M$. -/
@[category API, AMS 15 81]
theorem swappedUnnormalized_apply (i j : A × D) :
    swappedUnnormalized ρ τ M i j =
      ∑ x : B × C, ∑ y : B × C, ρ (i.1, x.1) (j.1, y.1) * τ (x.2, i.2) (y.2, j.2) * M y x := by
  classical
  simp [swappedUnnormalized, partialTraceMiddle, jointState, mul_apply,
    Fintype.sum_prod_type, one_apply]

/-- Product inputs leave the outside systems in their product, weighted by the middle outcome. -/
@[category test, AMS 15 81]
theorem swappedUnnormalized_product (X : Operator A) (Y : Operator B) (Z : Operator C)
    (W : Operator D) : swappedUnnormalized (X ⊗ₖ Y) (Z ⊗ₖ W) M =
      ((Y ⊗ₖ Z) * M).trace • (X ⊗ₖ W) := by
  ext i j
  simp only [swappedUnnormalized_apply, trace, diag, mul_apply, Matrix.smul_apply, smul_eq_mul,
    kronecker_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change (X _ _ * Y _ _) * (Z _ _ * W _ _) * _ = (Y _ _ * Z _ _ * _) * (X _ _ * W _ _)
  ring

end Swapping

/-- The original state assertion for all finite local dimensions. -/
def PPTSwappingConjecture : Prop :=
  ∀ (a b c d : ℕ) (ρ : Operator (Fin a × Fin b)) (τ : Operator (Fin c × Fin d))
    (M : Operator (Fin b × Fin c)), IsDensityMatrix ρ → IsPPT ρ → IsDensityMatrix τ →
    IsPPT τ → M.PosSemidef → successWeight ρ τ M ≠ 0 → IsSeparable (swappedState ρ τ M)

/-- In the input-output convention, the $(i,j)$ block of the Choi matrix is $\Phi(E_{ij})$. -/
def choiMatrix [DecidableEq A] (Φ : Operator A →ₗ[ℂ] Operator B) : Operator (A × B) :=
  fun i j ↦ Φ (Matrix.single i.1 j.1 1) i.2 j.2

/-- A maximally entangled measurement on the shared systems contracts two Choi matrices to the
Choi matrix of the composition, with the first map applied first. -/
@[category test, AMS 15 47 81]
theorem swappedUnnormalized_choiMatrix [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (Φ : Operator A →ₗ[ℂ] Operator B) (Ψ : Operator B →ₗ[ℂ] Operator C) :
    swappedUnnormalized (choiMatrix Φ) (choiMatrix Ψ) (maximallyEntangledOperator B) =
      choiMatrix (Ψ.comp Φ) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  let X := Φ (single i j 1)
  have hX : X = ∑ b, ∑ c, X b c • single b c (1 : ℂ) := by
    simpa [Matrix.smul_single] using matrix_eq_sum_single X
  simp [swappedUnnormalized_apply, maximallyEntangledOperator, vecMulVec, Fintype.sum_prod_type,
    choiMatrix, mul_ite]
  change (∑ b, ∑ c, X b c * Ψ (single b c 1) u v) = Ψ X u v
  conv_rhs => rw [hX]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- Choi's criterion for complete positivity. -/
def IsCompletelyPositive [DecidableEq A] (Φ : Operator A →ₗ[ℂ] Operator B) : Prop :=
  (choiMatrix Φ).PosSemidef

/-- A completely positive map whose composition with output transposition is completely positive. -/
def IsPPTMap [DecidableEq A] (Φ : Operator A →ₗ[ℂ] Operator B) : Prop :=
  IsCompletelyPositive Φ ∧ (partialTransposeRight (choiMatrix Φ)).PosSemidef

/-- A map is entanglement breaking if its Choi matrix is in the separable cone. Nonnegative
coefficients can be absorbed into either positive factor. The empty sum covers the zero map. -/
def IsEntanglementBreaking [DecidableEq A] (Φ : Operator A →ₗ[ℂ] Operator B) : Prop :=
  ∃ (k : ℕ) (X : Fin k → Operator A) (Y : Fin k → Operator B),
    (∀ i, (X i).PosSemidef) ∧ (∀ i, (Y i).PosSemidef) ∧ choiMatrix Φ = ∑ i, X i ⊗ₖ Y i

/-- The two-map assertion for a composition through dimensions $a,b,c$. -/
def PPTCompositionConjecture (a b c : ℕ) : Prop :=
  ∀ (Φ : Operator (Fin a) →ₗ[ℂ] Operator (Fin b)) (Ψ : Operator (Fin b) →ₗ[ℂ] Operator (Fin c)),
    IsPPTMap Φ → IsPPTMap Ψ → IsEntanglementBreaking (Ψ.comp Φ)

/-- The channel square assertion on $M_d(\mathbb C)$. -/
def PPTSquareConjecture (d : ℕ) : Prop :=
  ∀ Φ : Operator (Fin d) →ₗ[ℂ] Operator (Fin d),
    IsPPTMap Φ → (∀ X, (Φ X).trace = X.trace) → IsEntanglementBreaking (Φ.comp Φ)

/-- The original entanglement-swapping conjecture is false. A maximally entangled measurement
on the middle systems of the dimension-ten Choi pair yields an entangled output, by
`swappedUnnormalized_choiMatrix` and OpenAI, Theorem 1.2. -/
@[category research solved, AMS 15 47 81 94]
theorem ppt_squared_conjecture : ¬ PPTSwappingConjecture := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- Two PPT maps on $M_{10}(\mathbb C)$ can have a non-entanglement-breaking composition
(OpenAI, Theorem 1.2). -/
@[category research solved, AMS 15 47 81 94, formal_proof using lean4 at
  "https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Quantum/DimensionTen/Main.lean#L90"]
theorem ppt_squared_conjecture.variants.dim_ten : ¬ PPTCompositionConjecture 10 10 10 := by
  sorry

/-- The two-map conjecture fails in general. -/
@[category research solved, AMS 15 47 81 94]
theorem ppt_squared_conjecture.variants.maps : ¬ ∀ a b c, PPTCompositionConjecture a b c :=
  fun h ↦ ppt_squared_conjecture.variants.dim_ten (h 10 10 10)

set_option linter.style.formal_proof_palomar false in
/-- A trace-preserving PPT channel on $M_{21}(\mathbb C)$ can have a square that is not
entanglement breaking (OpenAI, Theorem 1.3). -/
@[category research solved, AMS 15 47 81 94, formal_proof using lean4 at
  "https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Quantum/DimensionTen/Channel.lean#L140"]
theorem ppt_squared_conjecture.variants.dim_twenty_one : ¬ PPTSquareConjecture 21 := by
  sorry

/-- Even for trace-preserving maps, the channel square conjecture fails in general. -/
@[category research solved, AMS 15 47 81 94]
theorem ppt_squared_conjecture.variants.channel_square : ¬ ∀ d, PPTSquareConjecture d :=
  fun h ↦ ppt_squared_conjecture.variants.dim_twenty_one (h 21)

/-- The composition of two qubit PPT maps is entanglement breaking by the
Peres–Horodecki separability criterion on $\mathbb C^2\otimes\mathbb C^2$. -/
@[category research solved, AMS 15 47 81 94]
theorem ppt_squared_conjecture.variants.dim_two : PPTCompositionConjecture 2 2 2 := by
  sorry

/-- The two-map assertion holds on $M_3(\mathbb C)$ (Christandl–Müller-Hermes–Wolf and
Chen–Yang–Tang). -/
@[category research solved, AMS 15 47 81 94]
theorem ppt_squared_conjecture.variants.dim_three : PPTCompositionConjecture 3 3 3 := by
  sorry

/-- The composition of any two PPT maps on $M_4(\mathbb C)$ is entanglement breaking. -/
@[category research open, AMS 15 47 81 94]
theorem ppt_squared_conjecture.variants.dim_four : PPTCompositionConjecture 4 4 4 := by
  sorry

end

end OpenQuantumProblem38
