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
# Strong Nakayama Conjecture
*Reference:* [R.R. Colby and K.R. Fuller, A note on the Nakayama conjectures, Tsukuba J. Math. \textbf{14} (1990), no.~2, 343--352.](https://doi.org/10.21099/tkbjm/1496161457)

# Generalized Nakayama Conjecture
# Auslander-Reiten Conjecture
*Reference:*
[M. Auslander and I. Reiten, On a generalized version of the Nakayama conjecture, Proc. Amer. Math. Soc. 52 (1975), 69--74.](https://doi.org/10.1090/S0002-9939-1975-0389977-6)

# Tachikawa Conjectures
*Reference:* [H. Tachikawa, Quasi-Frobenius Rings and Generalizations: QF-3 and QF-1 Rings, Lecture Notes in Mathematics, vol. 351, Springer, Berlin–Heidelberg, 1973](https://doi.org/10.1007/BFb0060005)

# Nakayama Conjecture
*Reference:* [T. Nakayama, On algebras with complete homology. Abh. Math. Sem. Univ. Hamburg 22 (1958), 300–307.](https://doi.org/10.1007/BF02941960)
-/

open CategoryTheory Abelian Limits

universe u v w

namespace NakayamaConjectures

/-
Let $R$ be an artinian ring, $A$ an algebra of finite type and $M$ a finitely generated module over $A$-/
variable {R : Type u} {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A] [Module.Finite R A] (M : ModuleCat.{v} A) [Module.Finite A M.carrier]


include R in
/--
The Strong Nakayama Conjecture :
$$
\operatorname{Ext}^1_A(M,A) = 0
\quad \Longrightarrow  \quad
M = 0
$$
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem sNC : (∀ i : ℕ, Subsingleton (Ext M (.of A A) i)) → IsZero M := by
  sorry

include R in
/--
The Generalized Nakayama Conjecture :
If Ext^i(M,A) = 0 for any integer `i ≥ 0` then M is not simple.

Note that `Simple` here is in Finitely generated Modules but it is equivalent to being simple in Modules.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem gNC : ( ∀ i : ℕ, Subsingleton (Ext M (.of A A) i)) → ¬ Simple M := by
  sorry

include R
/--
Reference : TODO
-/
@[category research solved, AMS 16 18]
lemma sGNC_impl_gNC : type_of% (sNC (R := R) (A := A)) → type_of% (gNC (R := R) (A:= A)) := by
  sorry

include R in
/--
Auslander-Reiten-Conjecture - an equivalent formulation of gNC :
If Ext^i(M,M) = Ext^i(M,A) = 0 for any integer `i > 0` then `M` is projective.

Note that `Projective` here is in Finitely generated Modules but it is equivalent to being projective in Modules.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem aRC : ( ∀ i > 0 , Subsingleton (Ext M (.of A A) i) ∧ Subsingleton (Ext M M i)) → Projective M := by
  sorry

include R
/--
Reference: TODO
-/
@[category research solved, AMS 16 18]
lemma gNC_equiv_aRC : type_of% (gNC (R := R) (A := A)) ↔ type_of% (aRC (R := R) (A := A)) := by
  sorry

include R in
/--
First Tachikawa Conjecture:

If for any `p > 0` and `I` a finiyely generated module over `A` Ext^p(I,A)=0 thent `A`is self injective (injective as a left module over itself).

Note that there is an equivalent formulation :If Ext^p(A^*,A) = 0 for any integer `p > 0`, then A is self-injective.

A^* is defined as `A →ₗ[R] R` equiped with a structure of A module. But if `R`is not a field, in  order to get the right definition it may be necessary to replace `R` by some kind of injective enveloppe of `R` not yet available in mathlib. We state this version of the conjecture. at then end of the file.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem tC1 : ( ∀ p > 0, ∀ (I : FGModuleCat A),
  (Injective I) →
  Subsingleton (Ext ((.of A I.carrier)) (ModuleCat.of A A) p) → CategoryTheory.Injective (ModuleCat.of A A))
  → Injective (ModuleCat.of A A)
 := by
  sorry

include R in
/--
Second Tachikawa Conjecture :
Let A be a finite-dimensional, self-injective algebra. For any A-module M with Ext^p(M,M) = 0 for any integer `p > 0`, it follows that M is projective.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem tC2 : (Injective (ModuleCat.of A A) → ∀ p > 0,
  Subsingleton (Ext M M p)) → Projective (ModuleCat.of A M ) := by
  sorry

include R in
/--
Nakayama Conjecture :
As in the First Tachikawa Conjecture there is an aquivalent formulation with the dual :

for every finitely genretaed module `M` over `A` if for all ì > 0 Extî(M ⊕ A^*, M ⊕ A) = 0 then `M` is projective.

We state the following version : if `A`has a projective-injective resolution then `A`is self injective.
-/
@[category research open, AMS 16 18]
theorem nC : (∃ I : InjectiveResolution (ModuleCat.of A A ), ∀ n, Projective <| I.cocomplex.X n) → Injective (ModuleCat.of A A ) := by
  sorry

/--
In this situation, nC is equivalent to the conjunction of the two Tachikawa's conjectures
ref : TODO
-/
@[category research solved, AMS 16 18]
lemma nC_equiv_tC1_and_tC2 :
    type_of% (tC1 (R := R) (A := A) ) ∧ type_of% (tC2 (R := R) (A := A)) ↔ type_of% (nC (R := R) (A := A)) := by
  sorry

end NakayamaConjectures

namespace NakayamaConjecturesOverFields

variable {R : Type u} {A : Type v} [Field R] [Ring A] [Algebra R A] [Module.Finite R A] (M : ModuleCat.{v} A) [Module.Finite A M.carrier]

variable (R A) in
abbrev dual := (A →ₗ[R] R)

instance : Module A (dual R A) := by
  have : A ≃+* (Aᵐᵒᵖ)ᵈᵐᵃ := RingEquiv.opOp _
  apply Module.compHom _ (this.toRingHom)

/--
Gorenstein Symmetry Conjecture
-/
@[category research open, AMS 16 18]
theorem gSC : injectiveDimension (ModuleCat.of A A) < ⊤ → projectiveDimension (ModuleCat.of A (dual R A)) < ⊤ := by
  sorry

/- in order to take Ext groups of dual R A with some other `ModuleCat.{v}` we need to have `R` and `A` leaving on the same universe-/
variable {R A : Type u} [Field R] [Ring A] [Algebra R A] [Module.Finite R A] (M : ModuleCat A) [Module.Finite A M.carrier]

/--
sNC expressed with the dual
-/
@[category research open, AMS 16 18]
theorem sNC_with_dual : IsZero M ∨ ∃ i, ¬ Subsingleton (Ext (.of A (dual R A )) M i) := by
  sorry

/--
In this situation, sNC_with_dual and sNC are equivalent,
ref : TODO
-/
@[category research solved, AMS 16 18]
lemma sNC_equiv : type_of% (NakayamaConjectures.sNC (R := R) (A := A)) ↔ type_of% (sNC_with_dual (R := R) (A := A)) := by sorry


/--
nC expressed with the dual
-/
@[category research open, AMS 16 18]
theorem nC_with_dual : (∀ i > 0,
  Subsingleton (Ext M M i) ∧
  Subsingleton (Ext M (.of A A) i) ∧
  Subsingleton (Ext (.of A (dual R A)) M i) ∧
  Subsingleton (Ext ((.of A (dual R A))) (ModuleCat.of A A) i)) → Projective M := by
  sorry

/--
In this situation, nCdual and nC are equivalent,
ref : TODO
-/
@[category research solved, AMS 16 18]
lemma nC_equiv : type_of% (NakayamaConjectures.nC (R := R) (A := A)) ↔ type_of% (nC_with_dual (R:= R) M) := by sorry


end NakayamaConjecturesOverFields
