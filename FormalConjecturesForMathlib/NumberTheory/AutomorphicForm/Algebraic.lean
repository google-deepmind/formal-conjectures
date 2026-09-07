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

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# Algebraic automorphic forms, after Gross

Let `G` be a definite connected reductive group over `ℚ`, so that `G(ℝ)` is compact. Gross's
*algebraic modular forms* are the functions on `G(𝔸_f)` that are right invariant under a level
`K_f` and transform under `G(ℚ)` through a weight `V`.

Definition 9 of [Loeffler] states: an algebraic automorphic form for `G` of level `K_f` and
weight `V` is a function `φ : G(𝔸_f) → V` such that

* `φ (g * k) = φ g` for all `g ∈ G(𝔸_f)` and `k ∈ K_f`;
* `φ (γ * g) = γ • φ g` for all `g ∈ G(𝔸_f)` and `γ ∈ G(ℚ)`.

The definition uses nothing about adeles: it makes sense for any group `G`, any two subgroups
`Γ` and `K` of `G` (playing the roles of `G(ℚ)` and `K_f`), and any `Γ`-representation `V`.
That is the generality used here, so that the arithmetic input — the choice of a definite
group and the finiteness of its class set — enters only when the definition is applied.

## Main declarations

* `algebraicAutomorphicForm Γ K R V`: the `R`-module of algebraic automorphic forms of level
  `K` and weight `V`, as a submodule of `G → V`.
* `AlgebraicAutomorphicForm.smul_apply_self`: the value of a form at `x` is fixed by the group
  `Γ_x = Γ ⊓ x K x⁻¹`, so it lies in `V ^ Γ_x`.
* `AlgebraicAutomorphicForm.eval`: evaluation at a set of representatives of the class set
  `Γ \ G / K`, and `AlgebraicAutomorphicForm.eval_injective`, which says a form is determined
  by those values.
* `AlgebraicAutomorphicForm.finiteDimensional`: consequently the space is finite-dimensional
  once the class set is finite and the weight is finite-dimensional.

## References

* [B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61-93][gross1999]
* [D. Loeffler, *Computing with algebraic automorphic forms*, §4][loeffler]
-/

variable {G : Type*} [Group G] (Γ K : Subgroup G)
variable (R : Type*) [CommRing R]
variable (V : Type*) [AddCommGroup V] [Module R V] [DistribMulAction Γ V]
  [SMulCommClass R Γ V]

/-- The space of algebraic automorphic forms of level `K` and weight `V`, for the subgroup `Γ`
of `G`: the functions `G → V` that are right invariant under `K` and `Γ`-equivariant on the
left. This is Definition 9 of Loeffler's notes, following Gross. -/
def algebraicAutomorphicForm : Submodule R (G → V) where
  carrier := {φ | (∀ (g : G) (k : K), φ (g * (k : G)) = φ g) ∧
    ∀ (g : G) (γ : Γ), φ ((γ : G) * g) = γ • φ g}
  zero_mem' := ⟨fun _ _ => rfl, fun _ γ => (smul_zero γ).symm⟩
  add_mem' {a b} ha hb :=
    ⟨fun g k => by simp only [Pi.add_apply, ha.1 g k, hb.1 g k],
     fun g γ => by simp only [Pi.add_apply, ha.2 g γ, hb.2 g γ, smul_add]⟩
  smul_mem' r a ha :=
    ⟨fun g k => by simp only [Pi.smul_apply, ha.1 g k],
     fun g γ => by simp only [Pi.smul_apply, ha.2 g γ, smul_comm]⟩

namespace AlgebraicAutomorphicForm

variable {Γ K R V}

lemma mem_iff {φ : G → V} :
    φ ∈ algebraicAutomorphicForm Γ K R V ↔
      (∀ (g : G) (k : K), φ (g * (k : G)) = φ g) ∧
        ∀ (g : G) (γ : Γ), φ ((γ : G) * g) = γ • φ g := Iff.rfl

lemma apply_mul_right {φ : G → V} (hφ : φ ∈ algebraicAutomorphicForm Γ K R V) (g : G)
    {k : G} (hk : k ∈ K) : φ (g * k) = φ g :=
  hφ.1 g ⟨k, hk⟩

lemma apply_mul_left {φ : G → V} (hφ : φ ∈ algebraicAutomorphicForm Γ K R V) {γ : G}
    (hγ : γ ∈ Γ) (g : G) : φ (γ * g) = (⟨γ, hγ⟩ : Γ) • φ g :=
  hφ.2 g ⟨γ, hγ⟩

/-- The value of an algebraic automorphic form at `x` is fixed by the group
`Γ_x = Γ ⊓ x K x⁻¹`; in Gross's notation, `φ x ∈ V ^ Γ_x`. -/
lemma smul_apply_self {φ : G → V} (hφ : φ ∈ algebraicAutomorphicForm Γ K R V) (x : G)
    {γ : G} (hγ : γ ∈ Γ) (hγK : x⁻¹ * γ * x ∈ K) :
    (⟨γ, hγ⟩ : Γ) • φ x = φ x := by
  have h : φ (γ * x) = (⟨γ, hγ⟩ : Γ) • φ x := apply_mul_left hφ hγ x
  rw [show γ * x = x * (x⁻¹ * γ * x) by rw [← mul_assoc, mul_inv_cancel_left],
    apply_mul_right hφ x hγK] at h
  exact h.symm

/-- An algebraic automorphic form is `Γ`-equivariant and `K`-invariant on both sides at once:
`φ (γ * x * k) = γ • φ x`. -/
lemma apply_mul_mul {φ : G → V} (hφ : φ ∈ algebraicAutomorphicForm Γ K R V) {γ : G}
    (hγ : γ ∈ Γ) (x : G) {k : G} (hk : k ∈ K) :
    φ (γ * x * k) = (⟨γ, hγ⟩ : Γ) • φ x := by
  rw [mul_assoc, apply_mul_left hφ hγ, apply_mul_right hφ x hk]

variable (Γ K R V)

/-- Evaluation of algebraic automorphic forms on the class set `Γ \ G / K`, using the chosen
representatives `Quotient.out`. -/
noncomputable def eval :
    algebraicAutomorphicForm Γ K R V →ₗ[R] (DoubleCoset.Quotient (Γ : Set G) (K : Set G) → V) where
  toFun φ q := (φ : G → V) (Quotient.out q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma eval_apply (φ : algebraicAutomorphicForm Γ K R V)
    (q : DoubleCoset.Quotient (Γ : Set G) (K : Set G)) :
    eval Γ K R V φ q = (φ : G → V) (Quotient.out q) := rfl

/-- An algebraic automorphic form is determined by its values on a set of representatives for
the class set `Γ \ G / K`. -/
lemma eval_injective : Function.Injective (eval Γ K R V) := by
  intro φ ψ h
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨a, ha, b, hb, hx⟩ :=
    (DoubleCoset.eq Γ K (Quotient.out (DoubleCoset.mk Γ K x)) x).1 (DoubleCoset.out_eq' Γ K _)
  have key : ∀ φ : G → V, φ ∈ algebraicAutomorphicForm Γ K R V →
      φ x = (⟨a, ha⟩ : Γ) • φ (Quotient.out (DoubleCoset.mk Γ K x)) := fun φ hφ => by
    conv_lhs => rw [hx]
    exact apply_mul_mul hφ ha _ hb
  have hout : (φ : G → V) (Quotient.out (DoubleCoset.mk Γ K x))
      = (ψ : G → V) (Quotient.out (DoubleCoset.mk Γ K x)) := congrFun h (DoubleCoset.mk Γ K x)
  rw [key _ φ.2, key _ ψ.2, hout]

end AlgebraicAutomorphicForm

section Field

variable {R V}
variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W] [DistribMulAction Γ W]
  [SMulCommClass F Γ W]

/-- Gross's finiteness theorem: if the class set `Γ \ G / K` is finite and the weight is
finite-dimensional, then the space of algebraic automorphic forms is finite-dimensional. For a
definite reductive group `G` and a compact open level `K` both hypotheses hold. -/
lemma AlgebraicAutomorphicForm.finiteDimensional
    [Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))] [FiniteDimensional F W] :
    FiniteDimensional F (algebraicAutomorphicForm Γ K F W) :=
  Module.Finite.of_injective (AlgebraicAutomorphicForm.eval Γ K F W)
    (AlgebraicAutomorphicForm.eval_injective Γ K F W)

end Field
