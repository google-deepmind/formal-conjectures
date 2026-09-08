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
# Finite generation of the cohomology of finite-dimensional Hopf algebras

Let $A$ be a finite-dimensional Hopf algebra over a field $k$, and view $k$ as an $A$-module
through the counit. The cohomology ring
$$H^*(A, k) = \mathrm{Ext}^*_A(k, k) = \bigoplus_{n \ge 0} \mathrm{Ext}^n_A(k, k)$$
is a graded-commutative $k$-algebra under the Yoneda product. Etingof and Ostrik conjecture that
it is a finitely generated $k$-algebra, and that $\mathrm{Ext}^*_A(k, M)$ is a finitely generated
module over it for every finite-dimensional $A$-module $M$. They state the conjecture for every
finite tensor category; the finite-dimensional modules over a finite-dimensional Hopf algebra form
the main class of examples, and the conjecture is open already in this case.

The conjecture holds when $A$ is cocommutative, that is, when $A$ is the group algebra of a finite
group scheme (Friedlander–Suslin). For the group algebra $k[G]$ of a finite group $G$ it is the
theorem of Evens and Venkov. Etingof and Ostrik note that it also holds when $A$ is commutative.

*References:*
* [arXiv:math/0301027](https://arxiv.org/abs/math/0301027) P. Etingof, V. Ostrik, *Finite tensor
  categories*, Mosc. Math. J. 4 (2004), no. 3, 627–654; Conjecture 2.18.
* [Friedlander–Suslin](https://doi.org/10.1007/s002220050119) E. M. Friedlander, A. Suslin,
  *Cohomology of finite group schemes over a field*, Invent. Math. 127 (1997), 209–270.
* [Evens](https://doi.org/10.1090/S0002-9947-1961-0137742-1) L. Evens, *The cohomology ring of a
  finite group*, Trans. Amer. Math. Soc. 101 (1961), 224–239.
-/

open CategoryTheory Abelian Bialgebra
open scoped DirectSum ModuleCat.Algebra

universe u

namespace HopfAlgebraCohomology

section Definitions

variable (k : Type u) [Field k] (A : Type u) [Ring A] [Bialgebra k A]

/-- The cohomology ring $H^*(A, k) = \mathrm{Ext}^*_A(k, k)$ of the bialgebra $A$ over $k$, where
$k$ is the trivial $A$-module through the counit and `Ext` is taken in `ModuleCat A`, the category
of all $A$-modules. It is a graded $k$-algebra under the Yoneda product. -/
abbrev cohomologyRing : Type u :=
  ⨁ n, Ext (trivialModuleCat k A) (trivialModuleCat k A) n

/-- The cohomology $H^*(A, M) = \mathrm{Ext}^*_A(k, M)$ of the bialgebra $A$ over $k$ with
coefficients in the $A$-module $M$. It is a graded module over `cohomologyRing k A` under the
Yoneda product. -/
abbrev cohomology (M : ModuleCat.{u} A) : Type u :=
  ⨁ n, Ext (trivialModuleCat k A) M n

variable {k A}

/-- The product on `cohomologyRing k A` is the Yoneda composition of extensions. -/
@[category API, AMS 16 18]
theorem of_mul_of {a b : ℕ} (x : Ext (trivialModuleCat k A) (trivialModuleCat k A) a)
    (y : Ext (trivialModuleCat k A) (trivialModuleCat k A) b) :
    (DirectSum.of _ a x : cohomologyRing k A) * DirectSum.of _ b y =
      DirectSum.of _ (a + b) (x.comp y rfl) :=
  DirectSum.of_mul_of x y

variable (k A) in
/-- A scalar $c \in k$ acts on `cohomologyRing k A` as $c$ times the identity in degree $0$. -/
@[category API, AMS 16 18]
theorem algebraMap_apply (c : k) :
    algebraMap k (cohomologyRing k A) c =
      DirectSum.of _ 0 (Ext.mk₀ (c • 𝟙 (trivialModuleCat k A))) :=
  rfl

/-- The action of `cohomologyRing k A` on `cohomology k A M` is the Yoneda composition of
extensions. -/
@[category API, AMS 16 18]
theorem of_smul_of {M : ModuleCat.{u} A} {a b : ℕ}
    (x : Ext (trivialModuleCat k A) (trivialModuleCat k A) a) (y : Ext (trivialModuleCat k A) M b) :
    (DirectSum.of _ a x : cohomologyRing k A) • (DirectSum.of _ b y : cohomology k A M) =
      DirectSum.of _ (a + b) (x.comp y rfl) :=
  DirectSum.Gmodule.of_smul_of (A := fun n ↦ Ext (trivialModuleCat k A) (trivialModuleCat k A) n)
    (M := fun n ↦ Ext (trivialModuleCat k A) M n) x y

variable (k A) in
/-- In degree $0$, the cohomology ring is the endomorphism ring of the trivial module. -/
@[category API, AMS 16 18]
theorem nonempty_addEquiv_zero :
    Nonempty (Ext (trivialModuleCat k A) (trivialModuleCat k A) 0 ≃+
      (trivialModuleCat k A ⟶ trivialModuleCat k A)) :=
  ⟨Ext.addEquiv₀⟩

end Definitions

variable (k : Type u) [Field k] (A : Type u) [Ring A] [HopfAlgebra k A] [FiniteDimensional k A]

/-- **Finite generation conjecture** (Etingof–Ostrik, Conjecture 2.18, algebra part).
For every finite-dimensional Hopf algebra $A$ over a field $k$, the cohomology ring
$H^*(A, k) = \mathrm{Ext}^*_A(k, k)$ is a finitely generated $k$-algebra. -/
@[category research open, AMS 16 18]
theorem cohomologyRing_finiteType : Algebra.FiniteType k (cohomologyRing k A) := by
  sorry

/-- **Finite generation conjecture** (Etingof–Ostrik, Conjecture 2.18, module part).
For every finite-dimensional Hopf algebra $A$ over a field $k$ and every finite-dimensional
$A$-module $M$, the cohomology $H^*(A, M) = \mathrm{Ext}^*_A(k, M)$ is a finitely generated module
over $H^*(A, k)$. -/
@[category research open, AMS 16 18]
theorem cohomology_finite (M : ModuleCat.{u} A) [FiniteDimensional k M] :
    Module.Finite (cohomologyRing k A) (cohomology k A M) := by
  sorry

/-- **Friedlander–Suslin.** If $A$ is a finite-dimensional cocommutative Hopf algebra over a
field $k$, that is, the group algebra of a finite group scheme over $k$, then $H^*(A, k)$ is a
finitely generated $k$-algebra. -/
@[category research solved, AMS 14 16 18]
theorem cohomologyRing_finiteType_of_isCocomm [Coalgebra.IsCocomm k A] :
    Algebra.FiniteType k (cohomologyRing k A) := by
  sorry

/-- **Friedlander–Suslin.** If $A$ is a finite-dimensional cocommutative Hopf algebra over a
field $k$ and $M$ is a finite-dimensional $A$-module, then $H^*(A, M)$ is a finitely generated
module over $H^*(A, k)$. -/
@[category research solved, AMS 14 16 18]
theorem cohomology_finite_of_isCocomm [Coalgebra.IsCocomm k A] (M : ModuleCat.{u} A)
    [FiniteDimensional k M] : Module.Finite (cohomologyRing k A) (cohomology k A M) := by
  sorry

/-- **Evens–Venkov.** For a finite group $G$ and a field $k$, the cohomology ring
$H^*(G, k) = \mathrm{Ext}^*_{k[G]}(k, k)$ of the group algebra $k[G]$ is a finitely generated
$k$-algebra. -/
@[category research solved, AMS 16 20]
theorem cohomologyRing_finiteType_monoidAlgebra (G : Type u) [Group G] [Finite G] :
    Algebra.FiniteType k (cohomologyRing k (MonoidAlgebra k G)) := by
  sorry

end HopfAlgebraCohomology
