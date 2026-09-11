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
# The Nakayama Conjectures

Let $R$ be a commutative Artinian ring and let $A$ be an Artin $R$-algebra, that is, an
$R$-algebra which is finitely generated as an $R$-module.
All modules are assumed to be finitely generated left $A$-modules.
The algebra $A$ is called *self-injective* if it is injective as a left module over itself.

This file collects the Nakayama Conjecture together with the family of homological conjectures
surrounding it.

* The **Nakayama Conjecture**: if $A$ has an injective resolution all of whose terms are
  projective, then $A$ is self-injective.
* The **Generalized Nakayama Conjecture**: a module $M$ with
  $\operatorname{Ext}^i_A(M, A) = 0$ for all $i \geq 0$ is not simple.
* The **Strong Nakayama Conjecture**: a module $M$ with
  $\operatorname{Ext}^i_A(M, A) = 0$ for all $i \geq 0$ is zero.
* The **Auslander-Reiten Conjecture**: a module $M$ with
  $\operatorname{Ext}^i_A(M, M) = \operatorname{Ext}^i_A(M, A) = 0$ for all $i > 0$ is
  projective. This conjecture has a separate entry.
* The **first Tachikawa Conjecture**: if $\operatorname{Ext}^i_A(I, A) = 0$ for all $i > 0$
  and all injective $I$, then $A$ is self-injective.
* The **second Tachikawa Conjecture**: if $A$ is self-injective, then a module $M$ with
  $\operatorname{Ext}^i_A(M, M) = 0$ for all $i > 0$ is projective.

The implications between them are
$$
\mathrm{snc} \implies \mathrm{gnc} \iff \mathrm{arc} \implies \mathrm{nc}
\iff \mathrm{tc1} \wedge \mathrm{tc2}.
$$

*References:*

The Strong Nakayama Conjecture was formulated by R. R. Colby and K. R. Fuller,
[A note on the Nakayama conjectures, Tsukuba J. Math. 14 (1990), no. 2, 343-352](https://doi.org/10.21099/tkbjm/1496161457),
where it is also shown to imply the Generalized Nakayama Conjecture.

The Generalized Nakayama Conjecture and its equivalence with the Auslander-Reiten Conjecture are
due to M. Auslander and I. Reiten,
[On a generalized version of the Nakayama conjecture, Proc. Amer. Math. Soc. 52 (1975), 69-74](https://doi.org/10.1090/S0002-9939-1975-0389977-6).

The Nakayama Conjecture was formulated by T. Nakayama in
[On algebras with complete homology, Abh. Math. Sem. Univ. Hamburg 22 (1958), 300-307](https://doi.org/10.1007/BF02941960).

The two Tachikawa Conjectures, and the fact that together they are equivalent to the Nakayama
Conjecture, appear in H. Tachikawa,
[Quasi-Frobenius Rings and Generalizations: QF-3 and QF-1 Rings, Lecture Notes in Mathematics, vol. 351, Springer, Berlin-Heidelberg, 1973](https://doi.org/10.1007/BFb0060005).
-/

open CategoryTheory Abelian Limits

universe u v

namespace NakayamaConjectures

/- Let `R` be a commutative Artinian ring, `A` an Artin `R`-algebra and `M` a finitely generated
`A`-module. -/
variable {R : Type u} {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A] (M : ModuleCat.{v} A) [Module.Finite A M.carrier]

include R in
/--
The **Strong Nakayama Conjecture**: For any finitely generated $A$-module $M$
$$
\operatorname{Ext}^i_A(M, A) = 0 \quad \text{for all } i \geq 0,
\quad \Longrightarrow \quad
M = 0
$$
-/
@[category research open, AMS 16 18]
theorem snc : (∀ i : ℕ, Subsingleton (Ext M (.of A A) i)) → IsZero M := by
  sorry

include R in
/--
The **Generalized Nakayama Conjecture**:
For any finitely generated $A$-module $M$
$$
\operatorname{Ext}^i_A(M, A) = 0 \quad \text{for all } i \geq 0,
\quad \Longrightarrow \quad
M \text{ is not simple}.
$$
-/
@[category research open, AMS 16 18]
theorem gnc : (∀ i : ℕ, Subsingleton (Ext M (.of A A) i)) → ¬ Simple M := by
  sorry

include R in
/--
The Strong Nakayama Conjecture implies the Generalized Nakayama Conjecture.
-/
@[category API, AMS 16 18]
lemma snc_imp_gnc : type_of% (snc (R := R) (A := A)) → type_of% (gnc (R := R) (A := A)) := by
  sorry


/-
The **Auslander-Reiten Conjecture**:
For any finitely generated $A$-module $M$
$$
\operatorname{Ext}^i_A(M, A) = \operatorname{Ext}^i_A(M, M) = 0 \quad \text{for all } i > 0,
\quad \Longrightarrow \quad
M \text{ is projective}.
$$
Once PR #5440 is merged, the equivalence can be stated as

@[category API, AMS 16 18]
lemma gnc_iff_arc : type_of% (gnc (R := R) (A := A)) ↔
    type_of% (ArtinAlgebra.auslander_reiten (R := R) (A := A)) := by
  sorry
-/

include R in
/--
The **first Tachikawa Conjecture**: if
$$
\operatorname{Ext}^p_A(I, A) = 0 \quad \text{for all } p > 0 \text{ and all injective } I,
$$
then $A$ is self-injective.

Injectivity of `I` is taken in the category of finitely generated $A$-modules, where it agrees
with injectivity as an $A$-module because $A$ is an Artin algebra. Every such `I` is a direct
summand of a finite direct sum of copies of $A^*$, so this is the usual formulation, which asks
only for the vanishing of $\operatorname{Ext}^p_A(A^*, A)$.
-/
@[category research open, AMS 16 18]
theorem tc1 : (∀ p > 0, ∀ I : FGModuleCat A, Injective I →
    Subsingleton (Ext (.of A I.carrier) (ModuleCat.of A A) p)) →
    Injective (ModuleCat.of A A) := by
  sorry

include R in
/--
The **second Tachikawa Conjecture**: if $A$ is self-injective and
$$
\operatorname{Ext}^i_A(M, M) = 0 \quad \text{for all } i > 0,
$$
then $M$ is projective.
-/
@[category research open, AMS 16 18]
theorem tc2 : Injective (ModuleCat.of A A) → (∀ p > 0, Subsingleton (Ext M M p)) →
    Projective M := by
  sorry

include R in
/--
The **Nakayama Conjecture**: if $A$ admits an injective resolution
$$
0 \to A \to I^0 \to I^1 \to \cdots
$$
in which every $I^n$ is projective, then $A$ is self-injective.

The conjecture is usually stated for the minimal injective resolution of $A$. The two forms
agree, because the minimal injective resolution is a direct summand of any injective resolution
and a direct summand of a projective module is projective.
-/
@[category research open, AMS 16 18]
theorem nc : (∃ I : InjectiveResolution (ModuleCat.of A A),
    ∀ n, Projective (I.cocomplex.X n)) → Injective (ModuleCat.of A A) := by
  sorry

include R in
/--
The Nakayama Conjecture is equivalent to the conjunction of the two Tachikawa Conjectures.
-/
@[category API, AMS 16 18]
lemma tc1_and_tc2_iff_nc :
    (type_of% @tc1 ∧ type_of% @tc2) ↔
      type_of% @nc := by
  sorry

end NakayamaConjectures

namespace Abelian
/-
The goal of this part is to define a version of duality in artinian algebra that does not require R to be a field.
-/

variable {C: Type u} [Category.{v} C] [Abelian C]
variable {M E : C} (u : M ⟶ E)

def IsEssentialExtension : Prop :=
  ∀ s : Subobject E, IsZero (Subobject.underlying.obj s) ∨ ¬ IsZero (pullback u ((MonoOver.forget E).obj (Subobject.representative.obj s)).hom)

def IsInjectiveHull : Prop := Injective E ∧ IsEssentialExtension u

variable (M)

class HasInjectiveHull : Prop where
  existsInjHull : ∃ E : C, ∃ u : M ⟶ E, IsInjectiveHull u

noncomputable def injectiveHull [HasInjectiveHull M] : C := (HasInjectiveHull.existsInjHull (M := M)).choose

noncomputable def injectiveHullHom [HasInjectiveHull M] : M ⟶ (injectiveHull M) := (HasInjectiveHull.existsInjHull (M := M)).choose_spec.choose

@[category API, AMS 18]
lemma IsInjectiveHullInjectiveHull [HasInjectiveHull M] : IsInjectiveHull (injectiveHullHom M) :=
  (HasInjectiveHull.existsInjHull (M := M)).choose_spec.choose_spec


@[category API, AMS 16 18]
instance [HasFilteredColimits C] [AB5 C] [EnoughInjectives C] : HasInjectiveHull M := by
  sorry

end Abelian

/- ## The dual formulations

There are variants of some of the previous conjectures that make usage of the dual of an artinian algebra.

Over a base field `k` the duality of an Artin algebra is the ordinary linear dual `(-)^* = Hom_k(-, k)`, (equiped with a structure of `A`module) so the conjectures take their customary form.

in the general case, the dual of `A` is `Hom_k(-, E(R/ Jacobson(R))`) (equiped with a structure of `A`module) with `E`being the injective enveloppe, defined in the previous section.

In order to keep `A`and `A^*`as `A`-modules in the same universe (wich is necessary to state the conjecture) we need (excpet for the definition of the dual ) to restrict to the case where `A`and `R`lives in the same universe. For that reason it remains uselfull to keep the previous version of the conjecture.

-/

namespace NakayamaConjecturesWithDuals

variable {R : Type u} {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A] [Module.Finite R A] (M : ModuleCat.{v} A) [Module.Finite A M.carrier]

variable (R A) in
abbrev dual := A →ₗ[R] (Abelian.injectiveHull (ModuleCat.of R (R ⧸ ((⊤:Ideal R).jacobson)))).carrier

/-- `A^*` is a left `A`-module, obtained by transporting its right `A`-module structure along
the isomorphism between `A` and the opposite of its opposite. -/
noncomputable instance : Module A (dual R A) := by
  have : A ≃+* (Aᵐᵒᵖ)ᵈᵐᵃ := RingEquiv.opOp _
  apply Module.compHom _ (this.toRingHom)

variable {R A : Type u} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A] [Module.Finite R A] (M : ModuleCat A) [Module.Finite A M.carrier]

/--
The Strong Nakayama Conjecture for finite-dimensional algebras in terms of the dual:
For any finitely generated $A$-module $M$
$$
\operatorname{Ext}^i_A(A^*, M) = 0 \quad \text{for all } i \geq 0,
\quad \Longrightarrow \quad
M = 0
$$
-/
@[category research open, AMS 16 18]
theorem snc_with_dual : IsZero M ∨ ∃ i, ¬ Subsingleton (Ext (.of A (dual R A)) M i) := by
  sorry

/-- The two formulations of the Strong Nakayama Conjecture agree. -/
@[category API, AMS 16 18]
lemma snc_iff_snc_with_dual :
    type_of% (NakayamaConjectures.snc (R := R) (A := A)) ↔
      type_of% (snc_with_dual (R:= R) (A := A)) := by
  sorry

/--
The Nakayama Conjecture in terms of the dual: if
$$
\operatorname{Ext}^i_A(M \oplus A^*, M \oplus A) = 0 \quad \text{for all } i > 0,
$$
then $M$ is projective.
-/
@[category research open, AMS 16 18]
theorem nc_with_dual : (∀ i > 0,
    Subsingleton (Ext M M i) ∧
    Subsingleton (Ext M (.of A A) i) ∧
    Subsingleton (Ext (.of A (dual R A)) M i) ∧
    Subsingleton (Ext (.of A (dual R A)) (ModuleCat.of A A) i)) → Projective M := by
  sorry

/-- The two formulations of the Nakayama Conjecture agree. -/
@[category API, AMS 16 18]
lemma nc_iff_nc_with_dual :
    type_of% (NakayamaConjectures.nc (R := R) (A := A)) ↔
      type_of% (nc_with_dual (R := R) (A := A)) := by
  sorry

end NakayamaConjecturesWithDuals
