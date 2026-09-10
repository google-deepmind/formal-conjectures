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

import FormalConjecturesUtil

/-!
# Mathoverflow 22078: is a smooth affine group scheme over the dual numbers linear?

Every affine group scheme of finite type over a field $k$ is a closed subgroup scheme of some
$\mathrm{GL}_n$. Brian Conrad asked whether this stays true over the ring of dual numbers
$k[\epsilon] = k[x]/(x^2)$, or over any artinian local ring. The proof over a field produces a
finite-dimensional subcomodule of the coordinate ring that generates it as an algebra, and uses
that a finitely generated submodule of the coordinate ring is free. Over $k[\epsilon]$ a finitely
generated submodule need not be free, and the argument breaks down.

The answer is no in characteristic zero. Push out the Heisenberg central extension
$1 \to \mathbb{G}_a \to H \to \mathbb{G}_a^2 \to 1$ over $k[\epsilon]$ along the homomorphism
$\mathbb{G}_a \to \mathbb{G}_m$, $x \mapsto 1 + \epsilon x$. This gives a smooth affine central
extension $1 \to \mathbb{G}_m \to G \to \mathbb{G}_a^2 \to 1$ with no faithful representation on
a finite free $k[\epsilon]$-module, so with no closed immersion into any $\mathrm{GL}_n$. Indeed,
such a representation $M$ is the direct sum of the weight spaces $M_i$ of the central
$\mathbb{G}_m$; each $M_i$ is a direct summand of $M$, hence free, and a subrepresentation. The
element $1 + \epsilon$ of $\mathbb{G}_m(k[\epsilon])$ is a commutator in $G(k[\epsilon])$, so it
acts on $M_i$ with determinant $1$. It acts by the scalar $1 + i\epsilon$, so that determinant is
$1 + i \operatorname{rank}(M_i)\epsilon$, forcing $i \operatorname{rank}(M_i) = 0$ in $k$. In
characteristic zero this kills every weight $i \neq 0$, so $\mathbb{G}_m$ acts trivially on $M$.
In characteristic $p$ the ranks may be multiples of $p$, the argument gives nothing, and the
question is open.

A group scheme is represented here by its coordinate Hopf algebra `A` over the base ring `R`.
`A` is not assumed to be cocommutative, so the group scheme is not assumed to be commutative.

*References:*
- [mathoverflow/22078](https://mathoverflow.net/questions/22078) asked by
  [*Brian Conrad*](https://mathoverflow.net/users/3927/bcnrd); the counterexample in
  characteristic zero is the [answer](https://mathoverflow.net/a/513098) by
  [*Akhil Mathew*](https://mathoverflow.net/users/594987/akhil-mathew).
- [B. Conrad, *Reductive group schemes*](http://math.stanford.edu/~conrad/papers/luminysga3.pdf),
  Rem. 2.3.3, which states the question and refers to [SGA 3], Exp. VIB, 13.2 and 13.5, and
  Exp. XI, 4.3.
- [F. Bruhat and J. Tits, *Groupes réductifs sur un corps local
  II*](http://www.numdam.org/item/PMIHES_1984__60__5_0/), 1.4.5, for the criterion used in
  `IsLinear` below and for the case of a Dedekind base.
- [G. Battiston and M. Romagny, *Representations of affine group schemes over general
  rings*](https://arxiv.org/abs/1807.01009), which claimed an affirmative answer over an artinian
  base and was withdrawn because of an error in its Thm. 4.1.
-/

namespace Mathoverflow22078

open Coalgebra TensorProduct

universe u v

/-- A square matrix `a` over a Hopf algebra `A` is *multiplicative* when
`Δ aᵢⱼ = ∑ₖ aᵢₖ ⊗ aₖⱼ` and `ε aᵢⱼ = δᵢⱼ`.

Multiplicative `n × n` matrices over `A` are exactly the homomorphisms of group schemes
`Spec A → GLₙ`: such a matrix is the image of the coordinates of `GLₙ` under the induced map of
Hopf algebras. No invertibility hypothesis is needed: the determinant of a multiplicative matrix
is group-like, hence a unit, by `IsMultiplicative.isGroupLikeElem_det` below. -/
structure IsMultiplicative (R : Type u) [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {n : ℕ} (a : Matrix (Fin n) (Fin n) A) : Prop where
  /-- The comultiplication of an entry is given by matrix multiplication. -/
  comul_apply : ∀ i j, comul (R := R) (a i j) = ∑ k, a i k ⊗ₜ[R] a k j
  /-- The counit of the matrix is the identity matrix. -/
  counit_apply : ∀ i j, counit (R := R) (a i j) = (1 : Matrix (Fin n) (Fin n) R) i j

/-- The affine group scheme `Spec A` over `R` is *linear* when it is a closed subgroup scheme of
some `GLₙ`.

By [BT84, 1.4.5] a homomorphism `Spec A → GLₙ` given by a multiplicative matrix `a` is a closed
immersion exactly when the entries of `a` together with `(det a)⁻¹` generate `A` as an
`R`-algebra. Asking instead that the entries alone generate `A` is equivalent: `(det a)⁻¹` is
group-like, so appending it as an extra diagonal entry turns `a` into a multiplicative
`(n + 1) × (n + 1)` matrix whose entries generate `A`. -/
def IsLinear (R : Type u) [CommRing R] (A : Type v) [CommRing A] [HopfAlgebra R A] : Prop :=
  ∃ (n : ℕ) (a : Matrix (Fin n) (Fin n) A), IsMultiplicative R a ∧
    Algebra.adjoin R (Set.range fun ij : Fin n × Fin n ↦ a ij.1 ij.2) = ⊤

/-- A `1 × 1` matrix is multiplicative exactly when its entry is group-like, that is, exactly
when it is a character `Spec A → GL₁ = 𝔾ₘ`. -/
@[category API, AMS 14 16]
theorem isMultiplicative_fin_one_iff (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [HopfAlgebra R A] (x : A) : IsMultiplicative R !![x] ↔ IsGroupLikeElem R x := by
  constructor
  · intro h
    exact ⟨by simpa using h.counit_apply 0 0, by simpa using h.comul_apply 0 0⟩
  · intro h
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩
    · fin_cases i; fin_cases j; simpa using h.comul_eq_tmul_self
    · fin_cases i; fin_cases j; simpa using h.counit_eq_one

/-- The determinant of a multiplicative matrix is a group-like element. It is therefore a unit,
by `IsGroupLikeElem.isUnit`, so a multiplicative matrix really does define a homomorphism of group
schemes into `GLₙ` and not merely into the monoid scheme of `n × n` matrices. -/
@[category API, AMS 14 16]
theorem IsMultiplicative.isGroupLikeElem_det {R : Type u} [CommRing R] {A : Type v} [CommRing A]
    [HopfAlgebra R A] {n : ℕ} {a : Matrix (Fin n) (Fin n) A} (h : IsMultiplicative R a) :
    IsGroupLikeElem R a.det where
  counit_eq_one := by
    have h1 : (Bialgebra.counitAlgHom R A).mapMatrix a = 1 := by
      ext i j
      simpa using h.counit_apply i j
    have h0 := AlgHom.map_det (Bialgebra.counitAlgHom R A) a
    rw [h1, Matrix.det_one] at h0
    simpa using h0
  comul_eq_tmul_self := by
    have h2 : (Bialgebra.comulAlgHom R A).mapMatrix a =
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := A)).mapMatrix a *
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A)).mapMatrix a := by
      ext i j
      rw [Matrix.mul_apply]
      simpa using h.comul_apply i j
    have h3 := AlgHom.map_det (Bialgebra.comulAlgHom R A) a
    rw [h2, Matrix.det_mul, ← AlgHom.map_det, ← AlgHom.map_det] at h3
    simpa using h3

/-- The trivial group scheme `Spec R` is linear, via the empty matrix. -/
@[category test, AMS 14 16]
theorem isLinear_self (R : Type u) [CommRing R] : IsLinear R R := by
  refine ⟨0, (0 : Matrix (Fin 0) (Fin 0) R), ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩, ?_⟩
  exact Subsingleton.elim _ _

open LaurentPolynomial in
/-- The multiplicative group `𝔾ₘ = Spec R[T, T⁻¹]` is linear: it is the diagonal torus
`diag(T, T⁻¹)` of `GL₂`. The `1 × 1` matrix `(T)` is multiplicative too, but `T` generates only
the polynomial subring `R[T]`, which is why a larger matrix is needed. -/
@[category test, AMS 14 16]
theorem isLinear_laurentPolynomial (R : Type u) [CommRing R] :
    IsLinear R (LaurentPolynomial R) := by
  refine ⟨2, !![T 1, 0; 0, T (-1)], ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, LaurentPolynomial.comul_T]
  · fin_cases i <;> fin_cases j <;> simp [LaurentPolynomial.counit_T]
  · set S := Algebra.adjoin R (Set.range fun ij : Fin 2 × Fin 2 ↦
      (!![T 1, 0; 0, T (-1)] : Matrix (Fin 2) (Fin 2) (LaurentPolynomial R)) ij.1 ij.2)
    have h1 : (T 1 : LaurentPolynomial R) ∈ S := Algebra.subset_adjoin ⟨(0, 0), by simp⟩
    have h2 : (T (-1) : LaurentPolynomial R) ∈ S := Algebra.subset_adjoin ⟨(1, 1), by simp⟩
    have hT : ∀ n : ℤ, (T n : LaurentPolynomial R) ∈ S := by
      intro n
      rcases le_or_gt 0 n with h | h
      · lift n to ℕ using h
        have : (T (n : ℤ) : LaurentPolynomial R) = T 1 ^ n := by simp
        rw [this]
        exact pow_mem h1 n
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
        have : (T (-(m : ℤ)) : LaurentPolynomial R) = T (-1) ^ m := by rw [T_pow]; ring_nf
        rw [this]
        exact pow_mem h2 m
    refine Algebra.eq_top_iff.2 fun p ↦ ?_
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq => exact add_mem hp hq
    | C_mul_T n a =>
      exact mul_mem (by rw [C_eq_algebraMap]; exact Subalgebra.algebraMap_mem S a) (hT n)

/--
Conrad's question: is every smooth affine group scheme over the ring of dual numbers
$k[\epsilon]$ a closed subgroup scheme of some $\mathrm{GL}_n$?

The answer is no: over a field of characteristic zero there is a counterexample.
-/
@[category research solved, AMS 14 16 20]
theorem isLinear_of_smooth_dualNumber : answer(False) ↔
    ∀ (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra (DualNumber k) A]
      [Algebra.Smooth (DualNumber k) A], IsLinear (DualNumber k) A := by
  sorry

/--
Over a field of characteristic zero there is a smooth affine group scheme over $k[\epsilon]$
that is not a closed subgroup scheme of any $\mathrm{GL}_n$, namely the pushout of the Heisenberg
extension of $\mathbb{G}_a^2$ by $\mathbb{G}_a$ along $\mathbb{G}_a \to \mathbb{G}_m$,
$x \mapsto 1 + \epsilon x$.
-/
@[category research solved, AMS 14 16 20]
theorem isLinear_of_smooth_dualNumber.variants.charZero (k : Type u) [Field k] [CharZero k] :
    ∃ (A : Type u) (_ : CommRing A) (_ : HopfAlgebra (DualNumber k) A)
      (_ : Algebra.Smooth (DualNumber k) A), ¬ IsLinear (DualNumber k) A := by
  sorry

/--
Is every smooth affine group scheme over $k[\epsilon]$, for $k$ a field of characteristic
$p > 0$, a closed subgroup scheme of some $\mathrm{GL}_n$? This case of Conrad's question is
open.
-/
@[category research open, AMS 14 16 20]
theorem isLinear_of_smooth_dualNumber.variants.charP : answer(sorry) ↔
    ∀ (p : ℕ) (_ : p.Prime) (k : Type u) [Field k] [CharP k p] (A : Type v) [CommRing A]
      [HopfAlgebra (DualNumber k) A] [Algebra.Smooth (DualNumber k) A],
      IsLinear (DualNumber k) A := by
  sorry

/--
Over a field every affine group scheme of finite type is a closed subgroup scheme of some
$\mathrm{GL}_n$. Smoothness is not needed.
-/
@[category textbook, AMS 14 16 20]
theorem isLinear_of_smooth_dualNumber.variants.field (k : Type u) [Field k] (A : Type v)
    [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A] : IsLinear k A := by
  sorry

/--
Over a Dedekind domain every flat affine group scheme of finite type is a closed subgroup scheme
of some $\mathrm{GL}_n$. This is [BT84, 1.4.5], which produces a closed immersion into
$\mathrm{GL}(M)$ for a finitely generated projective module $M$; choosing $N$ with $M \oplus N$
finite free embeds $\mathrm{GL}(M)$ into a $\mathrm{GL}_n$.
-/
@[category research solved, AMS 14 16 20]
theorem isLinear_of_smooth_dualNumber.variants.dedekindDomain (R : Type u) [CommRing R]
    [IsDedekindDomain R] (A : Type v) [CommRing A] [HopfAlgebra R A]
    [Algebra.FiniteType R A] [Module.Flat R A] : IsLinear R A := by
  sorry

end Mathoverflow22078
