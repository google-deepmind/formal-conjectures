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
# Open Quantum Problem 4: Catalytic majorization

**Problem:** Give an efficient criterion deciding when a bipartite pure state transformation
that is impossible under LOCC becomes possible in the presence of a *catalyst* state that is
returned unchanged.

By Nielsen's theorem, LOCC convertibility between bipartite pure states is governed by
majorization of their vectors of Schmidt eigenvalues. Allowing a catalyst corresponds to
**catalytic majorization** (also called **trumping**): given finite probability vectors $p$ and $q$,
there exists a finite probability vector $r$ such that
$$p \otimes r \prec q \otimes r.$$

By the Hardy–Littlewood–Pólya theorem, majorization $p \prec q$ holds if and only if $p = D q$
for some doubly stochastic matrix $D$. Using Mathlib's `doublyStochastic`, we formalize
majorization and catalytic majorization directly in terms of doubly stochastic matrices.

The problem was solved independently by Turgut (2007) and Klimesh (2007), who characterized
catalytic majorization by an explicit one-parameter family of additive strictly Schur-convex
functions $f_r$ ($r \in \mathbb{R}$) closely related to the Rényi entropies and the Burg entropy.

*References:*
- Open Quantum Problems, Problem 4:
  <https://oqp.iqoqi.oeaw.ac.at/catalytic-majorization>
- Solved Quantum Problems list:
  <https://oqp.iqoqi.oeaw.ac.at/solved-quantum-problems>
- Formal Conjectures issue #3404:
  <https://github.com/google-deepmind/formal-conjectures/issues/3404>
- O. Krüger and R. F. Werner,
  *Some Open Problems in Quantum Information Theory*,
  [arXiv:quant-ph/0504166](https://arxiv.org/abs/quant-ph/0504166) (2005).
- M. A. Nielsen,
  *Conditions for a class of entanglement transformations*,
  Phys. Rev. Lett. 83, 436–439 (1999),
  [arXiv:quant-ph/9811053](https://arxiv.org/abs/quant-ph/9811053).
- D. Jonathan and M. B. Plenio,
  *Entanglement-assisted local manipulation of pure quantum states*,
  Phys. Rev. Lett. 83, 3566–3569 (1999),
  [arXiv:quant-ph/9905071](https://arxiv.org/abs/quant-ph/9905071).
- S. Turgut,
  *Catalytic transformations for bipartite pure states*,
  J. Phys. A: Math. Theor. 40, 12185–12212 (2007),
  [arXiv:0707.0444](https://arxiv.org/abs/0707.0444).
- M. Klimesh,
  *Inequalities that Collectively Completely Characterize the Catalytic Majorization Relation*,
  [arXiv:0709.3680](https://arxiv.org/abs/0709.3680) (2007).
-/

@[expose] public section

open scoped BigOperators Matrix

namespace OpenQuantumProblem4

/-- A finite real vector is a probability vector if its entries are nonnegative and sum to `1`. -/
def IsProbabilityVector {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The Kronecker (tensor) product of two vectors. -/
def tensorProd {ι κ : Type*} (p : ι → ℝ) (r : κ → ℝ) : ι × κ → ℝ :=
  fun x => p x.1 * r x.2

/-- Majorization of finite real vectors via the Hardy–Littlewood–Pólya characterization:
`p ≺ q` iff `p = D *ᵥ q` for some doubly stochastic matrix `D`. -/
def Majorized {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι → ℝ) : Prop :=
  ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ q = p

/-- Catalytic majorization (trumping): `p ≺_T q` iff there exists a finite probability vector
`r : Fin c → ℝ` such that `p ⊗ r ≺ q ⊗ r`. -/
def CatalyticallyMajorized {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι → ℝ) : Prop :=
  ∃ (c : ℕ) (r : Fin c → ℝ), IsProbabilityVector r ∧ Majorized (tensorProd p r) (tensorProd q r)

/-- Two vectors on the same index type agree up to permutation of coordinates. -/
def IsPermEquivalent {ι : Type*} (p q : ι → ℝ) : Prop :=
  ∃ σ : Equiv.Perm ι, p = q ∘ σ

/-- Klimesh's one-parameter family of additive strictly Schur-convex functionals $f_r(p)$
([arXiv:0709.3680](https://arxiv.org/abs/0709.3680), Theorem 2), defined on strictly positive
probability vectors `p : Fin d → ℝ`:
- $f_r(p) = \ln \sum_i p_i^r$ for $r > 1$ or $r < 0$,
- $f_1(p) = \sum_i p_i \ln p_i$ (negative Shannon entropy),
- $f_r(p) = -\ln \sum_i p_i^r$ for $0 < r < 1$,
- $f_0(p) = -\frac{1}{d} \sum_i \ln p_i$ (normalized negative Burg entropy).

Up to positive scaling and sign conventions, these correspond to the classical Rényi entropies
(for $r \ne 0$) together with the log-product functional at $r = 0$. -/
noncomputable def klimeshFn {d : ℕ} (r : ℝ) (p : Fin d → ℝ) : ℝ :=
  if 1 < r then
    Real.log (∑ i, p i ^ r)
  else if r = 1 then
    ∑ i, p i * Real.log (p i)
  else if 0 < r then
    -Real.log (∑ i, p i ^ r)
  else if r = 0 then
    -(∑ i, Real.log (p i)) / (d : ℝ)
  else
    Real.log (∑ i, p i ^ r)

/-- Extended-real extension of Klimesh's functional `klimeshFn` to probability vectors that may
contain zero entries: for `r > 0` zero entries contribute `0` (as $0^r = 0$ and $0 \ln 0 = 0$),
while for `r ≤ 0` any zero entry sends the value to `⊤` (`+∞`). -/
noncomputable def klimeshFnEReal {d : ℕ} (r : ℝ) (p : Fin d → ℝ) : EReal :=
  if 0 < r then
    (klimeshFn r p : EReal)
  else if ∃ i, p i = 0 then
    ⊤
  else
    (klimeshFn r p : EReal)

/-! ## Basic API -/

/-- The tensor product of two probability vectors is a probability vector. -/
@[category API, AMS 15 81 94]
theorem isProbabilityVector_tensorProd {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → ℝ} {r : κ → ℝ} (hp : IsProbabilityVector p) (hr : IsProbabilityVector r) :
    IsProbabilityVector (tensorProd p r) := by
  refine ⟨fun x => mul_nonneg (hp.1 x.1) (hr.1 x.2), ?_⟩
  simp only [tensorProd, Fintype.sum_prod_type, ← Finset.mul_sum, hr.2, mul_one, hp.2]

/-- Majorization is reflexive. -/
@[category API, AMS 15 81 94]
theorem majorized_refl {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    Majorized p p :=
  ⟨1, one_mem _, Matrix.one_mulVec p⟩

/-- Majorization is transitive. -/
@[category API, AMS 15 81 94]
theorem majorized_trans {ι : Type*} [Fintype ι] [DecidableEq ι] {p q s : ι → ℝ}
    (hpq : Majorized p q) (hqs : Majorized q s) : Majorized p s := by
  rcases hpq with ⟨D₁, hD₁, h₁⟩
  rcases hqs with ⟨D₂, hD₂, h₂⟩
  exact ⟨D₁ * D₂, mul_mem hD₁ hD₂, by rw [← Matrix.mulVec_mulVec, h₂, h₁]⟩

/-- Permutation-equivalent vectors majorize each other. -/
@[category API, AMS 15 81 94]
theorem majorized_of_isPermEquivalent {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι → ℝ}
    (h : IsPermEquivalent p q) : Majorized p q := by
  rcases h with ⟨σ, rfl⟩
  exact ⟨σ.permMatrix ℝ, permMatrix_mem_doublyStochastic, Matrix.permMatrix_mulVec σ⟩

/-- Ordinary majorization implies catalytic majorization (using a trivial 1-dimensional catalyst). -/
@[category API, AMS 15 81 94]
theorem catalyticallyMajorized_of_majorized {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι → ℝ}
    (h : Majorized p q) : CatalyticallyMajorized p q := by
  rcases h with ⟨D, hD, hDq⟩
  refine ⟨1, fun _ => 1, ⟨fun _ => zero_le_one, by simp⟩, ?_⟩
  let e : ι ≃ ι × Fin 1 := Equiv.prodUnique ι (Fin 1) |>.symm
  refine ⟨D.reindex e e, reindex_mem_doublyStochastic hD, ?_⟩
  ext ⟨i, j⟩
  fin_cases j
  have hrow := congr_fun hDq i
  simpa [e, tensorProd, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Fintype.sum_prod_type] using hrow

/-- Catalytic majorization is reflexive. -/
@[category API, AMS 15 81 94]
theorem catalyticallyMajorized_refl {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    CatalyticallyMajorized p p :=
  catalyticallyMajorized_of_majorized (majorized_refl p)

/-! ## Main solved statements (Klimesh 2007 / Turgut 2007) -/

/--
**Open Quantum Problem #4 (Catalytic majorization — strictly positive case):**
Let $p, q \in \mathbb{R}^d$ be strictly positive probability vectors that are not permutations of
each other. Then $p$ is catalytically majorized by $q$ (i.e. there exists a finite probability
vector $r$ with $p \otimes r \prec q \otimes r$) if and only if $f_r(p) < f_r(q)$ for every
$r \in \mathbb{R}$, where $f_r$ is Klimesh's one-parameter family of Rényi/Burg functionals.

Proved independently by Turgut ([arXiv:0707.0444](https://arxiv.org/abs/0707.0444)) and
Klimesh ([arXiv:0709.3680](https://arxiv.org/abs/0709.3680), Theorem 2).
-/
@[category research solved, AMS 15 81 94]
theorem catalytic_majorization_positive {d : ℕ} {p q : Fin d → ℝ}
    (hp : IsProbabilityVector p) (hq : IsProbabilityVector q)
    (hp_pos : ∀ i, 0 < p i) (hq_pos : ∀ i, 0 < q i)
    (hneq : ¬ IsPermEquivalent p q) :
    CatalyticallyMajorized p q ↔ ∀ r : ℝ, klimeshFn r p < klimeshFn r q := by
  sorry

/--
**Open Quantum Problem #4 (Catalytic majorization — full Klimesh Theorem 2):**
Let $p, q \in \mathbb{R}^d$ be probability vectors that do not both contain a zero entry and are
not permutations of each other. Then $p$ is catalytically majorized by $q$ if and only if
$f_r(p) < f_r(q)$ in $\overline{\mathbb{R}}$ for every $r \in \mathbb{R}$.

Proved by Klimesh ([arXiv:0709.3680](https://arxiv.org/abs/0709.3680), Theorem 2) and
Turgut ([arXiv:0707.0444](https://arxiv.org/abs/0707.0444)).
-/
@[category research solved, AMS 15 81 94]
theorem catalytic_majorization {d : ℕ} {p q : Fin d → ℝ}
    (hp : IsProbabilityVector p) (hq : IsProbabilityVector q)
    (hzero : ¬ ((∃ i, p i = 0) ∧ (∃ i, q i = 0)))
    (hneq : ¬ IsPermEquivalent p q) :
    CatalyticallyMajorized p q ↔ ∀ r : ℝ, klimeshFnEReal r p < klimeshFnEReal r q := by
  sorry

/--
**Approximate catalytic majorization (OQP #4):**
For strictly positive probability vectors $p, q \in \mathbb{R}^d$, $p$ can be catalytically
transformed into arbitrarily close $\ell^1$-approximations of $q$ if and only if the non-strict
inequalities $f_r(p) \le f_r(q)$ hold for every $r \in \mathbb{R}$.
-/
@[category research solved, AMS 15 81 94]
theorem catalytic_majorization.variants.approximate {d : ℕ} {p q : Fin d → ℝ}
    (hp : IsProbabilityVector p) (hq : IsProbabilityVector q)
    (hp_pos : ∀ i, 0 < p i) (hq_pos : ∀ i, 0 < q i) :
    (∀ ε : ℝ, 0 < ε → ∃ q' : Fin d → ℝ, IsProbabilityVector q' ∧
      (∑ i, |q' i - q i|) < ε ∧ CatalyticallyMajorized p q') ↔
      ∀ r : ℝ, klimeshFn r p ≤ klimeshFn r q := by
  sorry

/-! ## Tests: The Jonathan–Plenio (1999) catalysis example -/

section Tests

/-- Scaled integer source vector $10 p = (4, 4, 1, 1)$ from Jonathan and Plenio (1999). -/
abbrev jonathanPlenioPN : Fin 4 → ℕ
  | 0 => 4
  | 1 => 4
  | 2 => 1
  | 3 => 1

/-- Scaled integer target vector $4 q = (2, 1, 1, 0)$ from Jonathan and Plenio (1999). -/
abbrev jonathanPlenioQN : Fin 4 → ℕ
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | 3 => 0

/-- Scaled integer catalyst vector $5 r = (3, 2)$ from Jonathan and Plenio (1999). -/
abbrev jonathanPlenioCatalystN : Fin 2 → ℕ
  | 0 => 3
  | 1 => 2

/-- Source vector $p = (0.4, 0.4, 0.1, 0.1)$ from Jonathan and Plenio (1999). -/
noncomputable def jonathanPlenioP : Fin 4 → ℝ := fun i => (jonathanPlenioPN i : ℝ) / 10

/-- Target vector $q = (0.5, 0.25, 0.25, 0)$ from Jonathan and Plenio (1999). -/
noncomputable def jonathanPlenioQ : Fin 4 → ℝ := fun i => (jonathanPlenioQN i : ℝ) / 4

/-- Catalyst vector $r = (0.6, 0.4)$ from Jonathan and Plenio (1999). -/
noncomputable def jonathanPlenioCatalyst : Fin 2 → ℝ := fun i => (jonathanPlenioCatalystN i : ℝ) / 5

/-- Scaled integer matrix $10 D$ for the explicit $8 \times 8$ block-diagonal doubly stochastic
matrix witnessing `(jonathanPlenioP ⊗ jonathanPlenioCatalyst) ≺ (jonathanPlenioQ ⊗ jonathanPlenioCatalyst)`. -/
abbrev jonathanPlenioMatrixN : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℕ
  | (0, 0), (0, 0) => 5
  | (0, 0), (0, 1) => 3
  | (0, 0), (1, 0) => 2
  | (1, 0), (0, 0) => 5
  | (1, 0), (0, 1) => 3
  | (1, 0), (2, 0) => 2
  | (0, 1), (0, 1) => 2
  | (0, 1), (1, 0) => 8
  | (1, 1), (0, 1) => 2
  | (1, 1), (2, 0) => 8
  | (2, 0), (1, 1) => 6
  | (2, 0), (3, 0) => 4
  | (3, 0), (2, 1) => 6
  | (3, 0), (3, 1) => 4
  | (2, 1), (1, 1) => 4
  | (2, 1), (3, 0) => 6
  | (3, 1), (2, 1) => 4
  | (3, 1), (3, 1) => 6
  | _, _ => 0

/-- Without a catalyst, $p = (0.4, 0.4, 0.1, 0.1)$ is NOT majorized by $q = (0.5, 0.25, 0.25, 0)$,
because $0.4 + 0.4 = 0.8 > 0.75 = 0.5 + 0.25$. -/
@[category test, AMS 15 81 94]
theorem jonathanPlenio_not_majorized : ¬ Majorized jonathanPlenioP jonathanPlenioQ := by
  rintro ⟨D, hD, hDq⟩
  have h0 : (D *ᵥ jonathanPlenioQ) 0 = 4 / 10 := by
    simpa [jonathanPlenioP, jonathanPlenioPN] using congr_fun hDq 0
  have h1 : (D *ᵥ jonathanPlenioQ) 1 = 4 / 10 := by
    simpa [jonathanPlenioP, jonathanPlenioPN] using congr_fun hDq 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, jonathanPlenioQ, jonathanPlenioQN,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, zero_div, mul_zero, add_zero] at h0 h1
  have hnonneg : ∀ i j, 0 ≤ D i j := fun i j => hD.1 i j
  have hrow0 : D 0 0 + D 0 1 + D 0 2 + D 0 3 = 1 := by
    simpa [Fin.sum_univ_four] using sum_row_of_mem_doublyStochastic hD 0
  have hrow1 : D 1 0 + D 1 1 + D 1 2 + D 1 3 = 1 := by
    simpa [Fin.sum_univ_four] using sum_row_of_mem_doublyStochastic hD 1
  have hcol0 : D 0 0 + D 1 0 + D 2 0 + D 3 0 = 1 := by
    simpa [Fin.sum_univ_four] using sum_col_of_mem_doublyStochastic hD 0
  have hcol1 : D 0 1 + D 1 1 + D 2 1 + D 3 1 = 1 := by
    simpa [Fin.sum_univ_four] using sum_col_of_mem_doublyStochastic hD 1
  have hcol2 : D 0 2 + D 1 2 + D 2 2 + D 3 2 = 1 := by
    simpa [Fin.sum_univ_four] using sum_col_of_mem_doublyStochastic hD 2
  have := hnonneg 0 3; have := hnonneg 1 3
  have := hnonneg 2 0; have := hnonneg 3 0
  have := hnonneg 2 1; have := hnonneg 3 1
  have := hnonneg 2 2; have := hnonneg 3 2
  linarith

/-- With the catalyst $r = (0.6, 0.4)$, Jonathan and Plenio (1999) showed that
$p \otimes r \prec q \otimes r$, demonstrating that catalytic majorization is strictly weaker
than ordinary majorization. -/
@[category test, AMS 15 81 94]
theorem jonathanPlenio_catalyticallyMajorized :
    CatalyticallyMajorized jonathanPlenioP jonathanPlenioQ := by
  have hr_sum : ∑ i : Fin 2, jonathanPlenioCatalystN i = 5 := by decide
  have hM_row : ∀ x : Fin 4 × Fin 2, ∑ y : Fin 4 × Fin 2, jonathanPlenioMatrixN x y = 10 := by
    decide
  have hM_col : ∀ y : Fin 4 × Fin 2, ∑ x : Fin 4 × Fin 2, jonathanPlenioMatrixN x y = 10 := by
    decide
  have hM_mul : ∀ x : Fin 4 × Fin 2,
      5 * ∑ y : Fin 4 × Fin 2,
        jonathanPlenioMatrixN x y * (jonathanPlenioQN y.1 * jonathanPlenioCatalystN y.2) =
      20 * (jonathanPlenioPN x.1 * jonathanPlenioCatalystN x.2) := by
    decide
  let D : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℝ :=
    Matrix.of fun x y => (jonathanPlenioMatrixN x y : ℝ) / 10
  refine ⟨2, jonathanPlenioCatalyst, ?_, D, ?_, ?_⟩
  · refine ⟨fun i => by simp only [jonathanPlenioCatalyst]; positivity, ?_⟩
    have hcast : (∑ i : Fin 2, (jonathanPlenioCatalystN i : ℝ)) = 5 := by
      exact_mod_cast hr_sum
    simp only [jonathanPlenioCatalyst, ← Finset.sum_div, hcast]
    norm_num
  · rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun x y => by simp only [D, Matrix.of_apply]; positivity, fun x => ?_, fun y => ?_⟩
    · have hcast : (∑ y : Fin 4 × Fin 2, (jonathanPlenioMatrixN x y : ℝ)) = 10 := by
        exact_mod_cast hM_row x
      simp only [D, Matrix.of_apply, ← Finset.sum_div, hcast]
      norm_num
    · have hcast : (∑ x : Fin 4 × Fin 2, (jonathanPlenioMatrixN x y : ℝ)) = 10 := by
        exact_mod_cast hM_col y
      simp only [D, Matrix.of_apply, ← Finset.sum_div, hcast]
      norm_num
  · ext x
    have hcast :
        (5 : ℝ) * ∑ y : Fin 4 × Fin 2,
          (jonathanPlenioMatrixN x y : ℝ) *
            ((jonathanPlenioQN y.1 : ℝ) * (jonathanPlenioCatalystN y.2 : ℝ)) =
        (20 : ℝ) * ((jonathanPlenioPN x.1 : ℝ) * (jonathanPlenioCatalystN x.2 : ℝ)) := by
      exact_mod_cast hM_mul x
    simp only [D, Matrix.mulVec, dotProduct, Matrix.of_apply, tensorProd,
      jonathanPlenioP, jonathanPlenioQ, jonathanPlenioCatalyst]
    have hsum :
        ∑ y : Fin 4 × Fin 2,
          ((jonathanPlenioMatrixN x y : ℝ) / 10) *
            (((jonathanPlenioQN y.1 : ℝ) / 4) * ((jonathanPlenioCatalystN y.2 : ℝ) / 5)) =
        (∑ y : Fin 4 × Fin 2,
          (jonathanPlenioMatrixN x y : ℝ) *
            ((jonathanPlenioQN y.1 : ℝ) * (jonathanPlenioCatalystN y.2 : ℝ))) / 200 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [hsum]
    linarith

end Tests

end OpenQuantumProblem4
