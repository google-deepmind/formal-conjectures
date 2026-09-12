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
is a graded-commutative $k$-algebra under the Yoneda product. The finite generation conjecture
asserts that it is a finitely generated $k$-algebra, and that $\mathrm{Ext}^*_A(k, M)$ is a
finitely generated module over it for every finite-dimensional $A$-module $M$. Etingof and Ostrik
state it for every finite tensor category; the finite-dimensional modules over a finite-dimensional
Hopf algebra form the main class of examples, and the conjecture is open already in this case.

The conjecture is not due to any one author. The question for a finite-dimensional Hopf algebra was
asked by a number of mathematicians and had circulated since at least the 1990s: Friedlander and
Suslin record it while expressly declining to answer it ("We do not know whether it is reasonable
to expect finite generation of the cohomology of an arbitrary finite dimensional Hopf algebra"),
and Friedlander and Negron later describe the conjecture as having "existed as a question at least
since the 90's" and as "recently stated explicitly in the work of Etingof and Ostrik". What Etingof
and Ostrik contribute is that explicit statement, together with its extension from Hopf algebras to
every finite tensor category; it is their Conjecture 2.18 that is formalised here.

The conjecture holds when $A$ is cocommutative, that is, when $A$ is the group algebra of a finite
group scheme (Friedlander–Suslin). For the group algebra $k[G]$ of a finite group $G$ it is the
theorem of Evens and Venkov, proved for a $p$-group by Golod. Etingof and Ostrik note that it also holds when $A$ is commutative.

Etingof and Ostrik work throughout the section containing the conjecture under the standing
assumption that $k$ is algebraically closed, whereas the statements below are for an arbitrary
field. The generalisation is valid. For a field extension $K/k$ one has
$\mathrm{Ext}^*_{A \otimes_k K}(K, K) \cong \mathrm{Ext}^*_A(k, k) \otimes_k K$, because $k$
admits a resolution by finitely generated free $A$-modules and $K$ is flat over $k$; and finite
generation descends, because the finitely many elements of $R = \mathrm{Ext}^*_A(k, k)$ occurring
in a finite set of $K$-algebra generators of $R \otimes_k K$ generate a $k$-subalgebra $R'$ with
$R' \otimes_k K = R \otimes_k K$, whence $R' = R$ by faithful flatness. The same argument applies
to the module statement. The theorems of Friedlander–Suslin and of Evens–Venkov are stated below
over an arbitrary field because that is the generality in which they are proved.

$\mathrm{Ext}$ is taken in the category of all $A$-modules rather than in the finite tensor
category of finite-dimensional ones. For finite-dimensional $A$ the two agree on
finite-dimensional modules, as the module docstring of
`FormalConjecturesForMathlib.RingTheory.Bialgebra.Cohomology` explains.

*References:*
* [arXiv:math/0301027](https://arxiv.org/abs/math/0301027) P. Etingof, V. Ostrik, *Finite tensor
  categories*, Mosc. Math. J. 4 (2004), no. 3, 627–654; Conjecture 2.18.
* [Friedlander–Suslin](https://doi.org/10.1007/s002220050119) E. M. Friedlander, A. Suslin,
  *Cohomology of finite group schemes over a field*, Invent. Math. 127 (1997), 209–270.
* [Evens](https://doi.org/10.1090/S0002-9947-1961-0137742-1) L. Evens, *The cohomology ring of a
  finite group*, Trans. Amer. Math. Soc. 101 (1961), 224–239.
* B. B. Venkov, *Cohomology algebras for some classifying spaces*, Dokl. Akad. Nauk SSSR 127
  (1959), 943–944.
* E. S. Golod, *The cohomology ring of a finite $p$-group*, Dokl. Akad. Nauk SSSR 125 (1959),
  703–706.
* [Friedlander–Negron](https://doi.org/10.2140/ant.2018.12.1281) E. M. Friedlander, C. Negron,
  *Cohomology for Drinfeld doubles of some infinitesimal group schemes*, Algebra Number Theory 12
  (2018), 1281–1309; the conjecture and its history, p. 1281.
* [Oberwolfach](https://doi.org/10.4171/OWR/2019/11) H. Krause, S. Witherspoon, J. J. Zhang
  (organisers), *Mini-Workshop: Cohomology of Hopf Algebras and Tensor Categories*, Oberwolfach
  Rep. (2019), 663–693; "asked by a number of mathematicians", p. 664.
-/

open Bialgebra
open scoped ModuleCat.Algebra

universe u

namespace HopfAlgebraCohomology

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

omit [FiniteDimensional k A] in
/-- Sanity check: taking the coefficient module `M` of the module statement to be `k` itself
gives back the cohomology ring. -/
@[category test, AMS 16 18]
theorem cohomology_trivialModuleCat :
    cohomology k A (trivialModuleCat k A) = cohomologyRing k A :=
  rfl

omit [FiniteDimensional k A] in
/-- Sanity check: the cohomology ring is not the zero ring, over which every finiteness statement
would hold trivially. -/
@[category test, AMS 16 18]
theorem cohomologyRing_nontrivial : Nontrivial (cohomologyRing k A) :=
  Bialgebra.nontrivial_cohomologyRing

end HopfAlgebraCohomology
