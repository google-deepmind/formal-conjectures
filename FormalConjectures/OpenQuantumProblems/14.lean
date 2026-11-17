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
# Open Quantum Problem 14: Tough error models

## Mathematical problem

An *error model* $\mathcal{E}$ is an $e$-dimensional vector space of operators acting on an
$n$-dimensional Hilbert space $\mathcal{H}$. A *quantum code* is a subspace
$\mathcal{C} \subseteq \mathcal{H}$, and it *corrects* $\mathcal{E}$ if the orthogonal projection
$P_{\mathcal{C}}$ onto $\mathcal{C}$ satisfies
$$P_{\mathcal{C}} A^* B P_{\mathcal{C}} = \lambda(A, B) P_{\mathcal{C}}$$
for all $A, B \in \mathcal{E}$ and suitable scalars $\lambda(A, B)$ (the Knill–Laflamme
condition).

Given $e$ and $n$, find the largest $c = c(e, n)$ such that one can assert the existence of a code
of dimension $c$ correcting $\mathcal{E}$ without further information about $\mathcal{E}$.

The problem page also asks for *tough* error models, for which this bound is (nearly) attained.
That part is not stated formally here.

## What this file formalizes

- `CorrectsErrors C E`: the code `C` corrects the error model `E`.
- `GuaranteesCode e n c`: every $e$-dimensional error model on $\mathbb{C}^n$ is corrected by
  some code of dimension $c$.
- `IsMaxGuaranteedCodeDim e n c`: $c = c(e, n)$, i.e. `GuaranteesCode e n c` holds and no larger
  value does.
- The open problem `tough_error_models` asks for the value of $c(e, n)$ for $e \le n^2$.

Choices made in the formalization:

- The Hilbert space is $\mathbb{C}^n$, as `EuclideanSpace ℂ (Fin n)`. Every $n$-dimensional
  complex Hilbert space is unitarily equivalent to it, and the correction condition is preserved
  by unitary equivalence.
- An error model is any complex subspace of operators of dimension $e$. It is not assumed to
  contain the identity, as the problem does not assume it.
- The scalar $\lambda(A, B)$ may be chosen separately for each pair $(A, B)$.
- $A^*$ is the adjoint, written `star A`.
- For $e > n^2$ there is no $e$-dimensional error model, so `GuaranteesCode e n c` holds for every
  $c$ and no maximum exists. The open problem therefore assumes $e \le n^2$. In that range
  $c(e, n)$ exists (`exists_isMaxGuaranteedCodeDim`) and lies between $1$ and $n$ when $n \ge 1$
  (`guaranteesCode_one`, `le_of_guaranteesCode`).

## Known bounds

- `guaranteesCode_one`: every error model is corrected by a code of dimension $1$, so
  $c(e, n) \ge 1$ for $n \ge 1$.
- `isMaxGuaranteedCodeDim_zero`: $c(0, n) = n$.
- `tough_error_models.variants.upper_bound`: $c(e, n) \le \lceil n/e \rceil$ for
  $1 \le e \le n^2$, the "trivial" bound of the problem page.
- `tough_error_models.variants.lower_bound_of_one_mem`: if the error model contains the
  identity, it is corrected by a code of dimension at least $n / (e^2(e^2 + 1))$ (Knill,
  Laflamme and Viola, Theorem 4).

The problem page states the lower bound as $c(e, n) > n / (e^2(e^2 + 1))$. Read literally for
this problem, which does not assume the identity in $\mathcal{E}$, the strict inequality fails:
`isMaxGuaranteedCodeDim_one_two` shows $c(1, 2) = 1 = 2 / (1 \cdot 2)$. Theorem 4 of Knill,
Laflamme and Viola gives only the non-strict bound, even when the identity is in $\mathcal{E}$.

## References

- IQOQI Vienna Open Quantum Problems, Problem 14:
  https://oqp.iqoqi.oeaw.ac.at/tough-error-models
- O. Krüger and R. F. Werner, *Some Open Problems in Quantum Information Theory*,
  arXiv:quant-ph/0504166 (2005), Problem 14.
- E. Knill, R. Laflamme and L. Viola, *Theory of Quantum Error Correction for General Noise*,
  Phys. Rev. Lett. 84, 2525 (2000), arXiv:quant-ph/9908066.
- E. Knill, R. Laflamme, A. Ashikhmin, H. Barnum, L. Viola and W. H. Zurek,
  *Introduction to Quantum Error Correction*, arXiv:quant-ph/0207170 (2002).
- Formal Conjectures issue #3420:
  https://github.com/google-deepmind/formal-conjectures/issues/3420
-/

@[expose] public section
noncomputable section
namespace OpenQuantumProblem14

/-- The $n$-dimensional Hilbert space $\mathbb{C}^n$. -/
abbrev Hilb (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- Operators on $\mathbb{C}^n$. -/
abbrev Op (n : ℕ) := Hilb n →L[ℂ] Hilb n

/-- The code `C` corrects the error model `E` (the Knill–Laflamme condition): for all
$A, B \in E$ there is a scalar $s$ with $P_C A^* B P_C = s P_C$. -/
def CorrectsErrors {n : ℕ} (C : Submodule ℂ (Hilb n)) (E : Submodule ℂ (Op n)) : Prop :=
  ∀ A ∈ E, ∀ B ∈ E, ∃ s : ℂ,
    C.starProjection * (star A * B) * C.starProjection = s • C.starProjection

/-- Every $e$-dimensional error model on $\mathbb{C}^n$ is corrected by some code of
dimension $c$. -/
def GuaranteesCode (e n c : ℕ) : Prop :=
  ∀ E : Submodule ℂ (Op n), Module.finrank ℂ E = e →
    ∃ C : Submodule ℂ (Hilb n), Module.finrank ℂ C = c ∧ CorrectsErrors C E

/-- $c$ is the largest code dimension guaranteed for every $e$-dimensional error model on
$\mathbb{C}^n$, i.e. $c = c(e, n)$. -/
def IsMaxGuaranteedCodeDim (e n c : ℕ) : Prop :=
  GuaranteesCode e n c ∧ ∀ m : ℕ, GuaranteesCode e n m → m ≤ c

/- ## Basic API -/

/-- The zero code corrects every error model. -/
@[category API, AMS 15 81 94]
lemma correctsErrors_bot {n : ℕ} (E : Submodule ℂ (Op n)) : CorrectsErrors ⊥ E := by
  intro A _ B _
  exact ⟨0, by simp [Submodule.starProjection_bot]⟩

/-- A one-dimensional code corrects every error model: $P X P = s P$ for every operator $X$
when $P$ has rank one. -/
@[category API, AMS 15 81 94]
lemma correctsErrors_span_singleton {n : ℕ} (v : Hilb n) (E : Submodule ℂ (Op n)) :
    CorrectsErrors (ℂ ∙ v) E := by
  intro A _ B _
  refine ⟨inner ℂ v ((star A * B) v) / (RCLike.ofReal (‖v‖ ^ 2) : ℂ), ?_⟩
  ext1 w
  set X := star A * B
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_singleton ℂ w, map_smul, map_smul,
    Submodule.starProjection_singleton ℂ (X v), smul_smul, smul_smul]
  congr 1
  ring

/-- `GuaranteesCode` holds for $c = 0$. -/
@[category API, AMS 15 81 94]
lemma guaranteesCode_zero (e n : ℕ) : GuaranteesCode e n 0 :=
  fun E _ => ⟨⊥, finrank_bot ℂ (Hilb n), correctsErrors_bot E⟩

/-- `GuaranteesCode` holds for $c = 1$ when $n \ge 1$: $c(e, n) \ge 1$. -/
@[category API, AMS 15 81 94]
lemma guaranteesCode_one (e : ℕ) {n : ℕ} (hn : 1 ≤ n) : GuaranteesCode e n 1 := by
  intro E _
  set v : Hilb n := EuclideanSpace.single ⟨0, hn⟩ 1
  have hv : v ≠ 0 := by simp [v]
  exact ⟨ℂ ∙ v, finrank_span_singleton hv, correctsErrors_span_singleton v E⟩

/-- A guaranteed code dimension is at most $n$, provided some $e$-dimensional error model
exists. -/
@[category API, AMS 15 81 94]
lemma le_of_guaranteesCode {e n c : ℕ} (E : Submodule ℂ (Op n)) (hE : Module.finrank ℂ E = e)
    (h : GuaranteesCode e n c) : c ≤ n := by
  obtain ⟨C, hC, -⟩ := h E hE
  simpa [hC] using Submodule.finrank_le C

/-- For $e \le n^2$ the value $c(e, n)$ exists: some $e$-dimensional error model exists, so the
guaranteed code dimensions are at most $n$, and $0$ is always guaranteed. -/
@[category API, AMS 15 81 94]
lemma exists_isMaxGuaranteedCodeDim {e n : ℕ} (he : e ≤ n ^ 2) :
    ∃ c, IsMaxGuaranteedCodeDim e n c := by
  classical
  have hdim : Module.finrank ℂ (Op n) = n ^ 2 := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := Hilb n) (F' := Hilb n)).finrank_eq,
      Module.finrank_linearMap, finrank_euclideanSpace_fin, sq]
  let b := Module.finBasisOfFinrankEq ℂ (Op n) hdim
  let E : Submodule ℂ (Op n) :=
    Submodule.span ℂ (Set.range (b ∘ Fin.castLE he))
  have hE : Module.finrank ℂ E = e := by
    rw [finrank_span_eq_card (b.linearIndependent.comp _ (Fin.castLE_injective he)),
      Fintype.card_fin]
  exact ⟨Nat.findGreatest (GuaranteesCode e n) n,
    Nat.findGreatest_spec (Nat.zero_le n) (guaranteesCode_zero e n),
    fun m hm => Nat.le_findGreatest (le_of_guaranteesCode E hE hm) hm⟩

/- ## Tests -/

/-- With no errors, the whole space is a code: $c(0, n) = n$. -/
@[category test, AMS 15 81 94]
theorem isMaxGuaranteedCodeDim_zero (n : ℕ) : IsMaxGuaranteedCodeDim 0 n n := by
  refine ⟨fun E hE => ⟨⊤, by simp, ?_⟩, fun m hm => le_of_guaranteesCode ⊥ (by simp) hm⟩
  rw [Submodule.finrank_eq_zero] at hE
  subst hE
  intro A hA B hB
  rw [Submodule.mem_bot] at hA hB
  exact ⟨0, by simp [hA, hB]⟩

/-- The error operator $\mathrm{diag}(1, 2)$ on $\mathbb{C}^2$. -/
def diagOneTwo : Op 2 :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (Matrix.diagonal ![1, 2])

/-- $c(1, 2) = 1$: the error model spanned by $\mathrm{diag}(1, 2)$ has no correcting code of
dimension $2$, since the only such code is $\mathbb{C}^2$ and $A^* A = \mathrm{diag}(1, 4)$ is not
a scalar. -/
@[category test, AMS 15 81 94]
theorem isMaxGuaranteedCodeDim_one_two : IsMaxGuaranteedCodeDim 1 2 1 := by
  refine ⟨guaranteesCode_one 1 (by norm_num), fun m hm => ?_⟩
  have hA : diagOneTwo ≠ 0 := by
    intro h
    have := congrArg (fun T : Op 2 => (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm T) h
    simp only [diagOneTwo, StarAlgEquiv.symm_apply_apply, map_zero] at this
    have := congrFun (congrFun this 0) 0
    simp at this
  obtain ⟨C, hC, hcorr⟩ := hm (ℂ ∙ diagOneTwo) (finrank_span_singleton hA)
  have hle : m ≤ 2 := by simpa [hC] using Submodule.finrank_le C
  by_contra hm1
  have hm2 : m = 2 := by omega
  have htop : C = ⊤ := Submodule.eq_top_of_finrank_eq (by simp [hC, hm2])
  subst htop
  obtain ⟨s, hs⟩ := hcorr diagOneTwo (Submodule.mem_span_singleton_self _) diagOneTwo
    (Submodule.mem_span_singleton_self _)
  rw [Submodule.starProjection_top', mul_one, one_mul] at hs
  have hmat : star (Matrix.diagonal ![(1 : ℂ), 2]) * Matrix.diagonal ![(1 : ℂ), 2] =
      s • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [diagOneTwo, ← map_star, ← map_mul] at hs
    have := congrArg (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm hs
    simpa using this
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal] at hmat
  have h0 := congrFun (congrFun hmat 0) 0
  have h1 := congrFun (congrFun hmat 1) 1
  simp at h0 h1
  rw [← h0, map_ofNat] at h1
  norm_num at h1

/- ## Known bounds -/

/-- The trivial upper bound $c(e, n) \le \lceil n/e \rceil$ for $1 \le e \le n^2$: some
$e$-dimensional error model has no correcting code of larger dimension. For $e \le n$, take the
span of $e$ orthogonal projections of rank about $n/e$ that sum to the identity. For $e > n$, take
an error model containing the $n$ rank-one projections onto the basis vectors. -/
@[category research solved, AMS 15 81 94]
theorem tough_error_models.variants.upper_bound (e n : ℕ) (he : 1 ≤ e) (hen : e ≤ n ^ 2) :
    ∃ E : Submodule ℂ (Op n), Module.finrank ℂ E = e ∧
      ∀ C : Submodule ℂ (Hilb n), CorrectsErrors C E →
        Module.finrank ℂ C ≤ ⌈(n : ℝ) / e⌉₊ := by
  sorry

/-- Knill, Laflamme and Viola, Theorem 4, for an $e$-dimensional error model containing the
identity: the products $A^* B$ span a $*$-closed space of dimension $D \le e^2$ containing the
identity, so some code of dimension at least $\lceil \lceil n/D \rceil / (D + 1) \rceil \ge
n / (e^2(e^2 + 1))$ corrects the error model. -/
@[category research solved, AMS 15 81 94]
theorem tough_error_models.variants.lower_bound_of_one_mem (e n : ℕ) (E : Submodule ℂ (Op n))
    (hE : Module.finrank ℂ E = e) (h1 : (1 : Op n) ∈ E) :
    ∃ C : Submodule ℂ (Hilb n), CorrectsErrors C E ∧
      (n : ℝ) / (e ^ 2 * (e ^ 2 + 1)) ≤ Module.finrank ℂ C := by
  sorry

/- ## The open problem -/

def tough_error_models.answer : ℕ → ℕ → ℕ := sorry

/-- Open Quantum Problem 14: determine $c(e, n)$, the largest code dimension guaranteed for every
$e$-dimensional error model on $\mathbb{C}^n$. -/
@[category research open, question value, AMS 15 81 94]
theorem tough_error_models (e n : ℕ) (he : e ≤ n ^ 2) :
    IsMaxGuaranteedCodeDim e n (tough_error_models.answer e n) := by
  sorry

end OpenQuantumProblem14
