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

open CategoryTheory Abelian Limits

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

universe u v w

/-
Let `R`be an artinian ring, `A` an algebra of finite type and `M`a finitely generated module over `A`-/
variable {R : Type u} {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A] [Module.Finite R A] {M : ModuleCat.{v} A} [Module.Finite A M.carrier]


namespace NakayamaConjectures

/--
The Strong Nakayama Conjecture:
If  Ext^i(M,A) = 0 for any integer `i ≥ 0` then M = 0.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem SNC (_ : ∀ i : ℕ, Subsingleton (Ext M (.of A A) i)) : IsZero M := by
  sorry

/--
The Generalized Nakayama Conjecture:
If Ext^i(M,A) = 0 for any integer `i ≥ 0` then M is not simple.

Note that `Simple` here is in Finitely generated Modules but it is equivalent to being simple in Modules.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem GNC (_ : ∀ i : ℕ, Subsingleton (Ext M (.of A A) i)) :
    ¬ Simple M := by
  sorry

/--
Auslander-Reiten-Conjecture - an equivalent formulation of GNC:
If Ext^i(M,M) = Ext^i(M,A) = 0 for any integer `i ≥ 0` then `M` is projective.

Note that `Projective` here is in Finitely generated Modules but it is equivalent to being projective in Modules.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem ARC (_ : ∀ i > 0 ,
        Subsingleton (Ext M (.of A A) i) ∧
        Subsingleton (Ext M M i)) :
        Projective M := by
  sorry

/--
First Tachikawa Conjecture:

If for any `p ≥ 0` and `I` a finiyely generated module over `A` Ext^p(I,A)=0 thent `A`is self injective (injective as a left module over itself).

Note that there is an equivalent formulation :If Ext^p(A^*,A) = 0 for any integer `p > 0`, then A is self-injective.

But A^* is defined as `A →ₗ[R] R` equiped with a structure of A module.
- An instance is given by `LinearMap.instModuleDomMulActOfSMulCommClass`but in order to have a good universe, we need to have `R`and `A` leaving in the same universe.
- In adition it's a module over `Aᵈᵐᵃ`wich is not `A`if `A`is not commutative.
- Finaly in order to get the right definition it may be necessary to replace `R` by some kind of injective enveloppe of `R` not yet availabla.

-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem TC1 (_ : ∀ p > 0, ∀ (I : FGModuleCat A), (Injective I) →
        Subsingleton (Ext ((.of A I.carrier)) (ModuleCat.of A A) p) →
        CategoryTheory.Injective (ModuleCat.of A A)) :
        Injective (ModuleCat.of A A) := by
    sorry

/--
Second Tachikawa Conjecture:
Let A be a finite-dimensional, self-injective algebra. For any A-module M with Ext^p(M,M) = 0 for any integer `p > 0`, it follows that M is projective.
-/
@[category research open, AMS 16 18] /- Associative rings and algebras + Category theory; homological algebra -/
theorem TC2 (_ : Injective (ModuleCat.of A A)) (_ : ∀ p > 0,
        Subsingleton (Ext M M p)) :
        Projective (ModuleCat.of A M ) := by
  sorry

/-
Nakayama Conjecture:
Let A be a finite-dimensional algebra.
-/

end NakayamaConjectures
