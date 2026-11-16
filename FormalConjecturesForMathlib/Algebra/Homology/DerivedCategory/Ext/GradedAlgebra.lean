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

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Module.GradedModule
public import FormalConjecturesForMathlib.Algebra.GradedMonoid

@[expose] public noncomputable section

/-!
# The Yoneda algebra of an object of an abelian category

Let `C` be an abelian category with `HasExt C` and let `X : C`. The Yoneda composition
`Ext.comp : Ext X X a → Ext X X b → Ext X X (a + b)` makes the family `fun n ↦ Ext X X n` a
graded ring, so that `⨁ n, Ext X X n` is a ring: the Yoneda algebra `Ext^*(X, X)` of `X`.
When `C` is `R`-linear for a commutative ring `R`, it is a graded `R`-algebra.
For `Y : C`, the family `fun n ↦ Ext X Y n` is a graded module over `fun n ↦ Ext X X n`, so
that `⨁ n, Ext X Y n` is a module over `⨁ n, Ext X X n`.

## Main declarations

* `CategoryTheory.Abelian.Ext.instGRing`: the graded ring structure on `fun n ↦ Ext X X n`.
* `CategoryTheory.Abelian.Ext.instGAlgebra`: the graded `R`-algebra structure on
  `fun n ↦ Ext X X n` when `C` is `R`-linear.
* `CategoryTheory.Abelian.Ext.instGmodule`: the graded module structure on `fun n ↦ Ext X Y n`
  over `fun n ↦ Ext X X n`.

The proofs of the graded axioms compare elements of `GradedMonoid` in different degrees; they use
`GradedMonoid.mk_eq_mk` and `Ext.comp_heq` to reduce these to equalities in a single degree.
-/

universe w t v u

open DirectSum

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section

variable {X Y Z : C}

/-- Up to `HEq`, the composition `Ext.comp` does not depend on the proof of the degree
equation. -/
lemma comp_heq {a b c c' : ℕ} (α : Ext X Y a) (β : Ext Y Z b) (h : a + b = c)
    (h' : a + b = c') : HEq (α.comp β h) (α.comp β h') := by
  subst h h'
  rfl

end

variable (X Y : C)

instance instGOne : GradedMonoid.GOne (fun n ↦ Ext X X n) where
  one := mk₀ (𝟙 X)

instance instGMul : GradedMonoid.GMul (fun n ↦ Ext X X n) where
  mul α β := α.comp β rfl

instance instGSMul : GradedMonoid.GSMul (fun n ↦ Ext X X n) (fun n ↦ Ext X Y n) where
  smul α β := α.comp β rfl

variable {X Y}

@[simp]
lemma gOne_eq : (GradedMonoid.GOne.one : Ext X X 0) = mk₀ (𝟙 X) := rfl

@[simp]
lemma gMul_eq {a b : ℕ} (α : Ext X X a) (β : Ext X X b) :
    GradedMonoid.GMul.mul α β = α.comp β rfl := rfl

@[simp]
lemma gSMul_eq {a b : ℕ} (α : Ext X X a) (β : Ext X Y b) :
    GradedMonoid.GSMul.smul α β = α.comp β rfl := rfl

variable (X Y)

instance instGMonoid : GradedMonoid.GMonoid (fun n ↦ Ext X X n) where
  one_mul := fun ⟨n, α⟩ ↦ Sigma.ext (zero_add n)
    ((comp_heq _ _ rfl (zero_add n)).trans (heq_of_eq (mk₀_id_comp α)))
  mul_one := fun ⟨n, α⟩ ↦ Sigma.ext (add_zero n)
    ((comp_heq _ _ rfl (add_zero n)).trans (heq_of_eq (comp_mk₀_id α)))
  mul_assoc := fun ⟨a, α⟩ ⟨b, β⟩ ⟨c, γ⟩ ↦ Sigma.ext (add_assoc a b c)
    ((heq_of_eq (comp_assoc α β γ rfl rfl rfl)).trans (comp_heq _ _ _ rfl))

instance instGRing : DirectSum.GRing (fun n ↦ Ext X X n) where
  mul_zero α := comp_zero α X _ _ rfl
  zero_mul β := zero_comp _ _ β _ rfl
  mul_add α β γ := comp_add α β γ rfl
  add_mul α β γ := add_comp α β γ rfl
  natCast n := n • mk₀ (𝟙 X)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul (mk₀ (𝟙 X)) n
  intCast n := n • mk₀ (𝟙 X)
  intCast_ofNat n := natCast_zsmul (mk₀ (𝟙 X)) n
  intCast_negSucc_ofNat n := negSucc_zsmul (mk₀ (𝟙 X)) n

instance instGmodule : DirectSum.Gmodule (fun n ↦ Ext X X n) (fun n ↦ Ext X Y n) where
  one_smul := fun ⟨n, β⟩ ↦ Sigma.ext (zero_add n)
    ((comp_heq _ _ rfl (zero_add n)).trans (heq_of_eq (mk₀_id_comp β)))
  mul_smul := fun ⟨a, α⟩ ⟨b, α'⟩ ⟨c, β⟩ ↦ Sigma.ext (add_assoc a b c)
    ((heq_of_eq (comp_assoc α α' β rfl rfl rfl)).trans (comp_heq _ _ _ rfl))
  smul_add α β β' := comp_add α β β' rfl
  smul_zero α := comp_zero α Y _ _ rfl
  add_smul α α' β := add_comp α α' β rfl
  zero_smul β := zero_comp _ _ β _ rfl

variable (R : Type t) [CommRing R] [Linear R C]

instance instGAlgebra : DirectSum.GAlgebra R (fun n ↦ Ext X X n) where
  toFun :=
    { toFun r := mk₀ (r • 𝟙 X)
      map_zero' := by simp
      map_add' r s := by simp [mk₀_smul, mk₀_add, add_smul] }
  map_one := by simp
  map_mul r s := GradedMonoid.mk_eq_mk rfl (heq_of_eq (by
    change mk₀ ((r * s) • 𝟙 X) = (mk₀ (r • 𝟙 X)).comp (mk₀ (s • 𝟙 X)) (zero_add 0)
    simp [smul_smul, mul_comm]))
  commutes r := fun ⟨n, α⟩ ↦ by
    change GradedMonoid.mk (0 + n) ((mk₀ (r • 𝟙 X)).comp α rfl) =
      GradedMonoid.mk (n + 0) (α.comp (mk₀ (r • 𝟙 X)) rfl)
    refine GradedMonoid.mk_eq_mk (by simp) ((comp_heq _ _ rfl (zero_add n)).trans
      ((heq_of_eq ?_).trans (comp_heq _ _ (add_zero n) rfl)))
    simp [mk₀_smul]
  smul_def r := fun ⟨n, α⟩ ↦ by
    change GradedMonoid.mk n (r • α) = GradedMonoid.mk (0 + n) ((mk₀ (r • 𝟙 X)).comp α rfl)
    exact GradedMonoid.mk_eq_mk (zero_add n).symm
      ((heq_of_eq (by simp [mk₀_smul])).trans (comp_heq _ _ (zero_add n) rfl))

end CategoryTheory.Abelian.Ext
