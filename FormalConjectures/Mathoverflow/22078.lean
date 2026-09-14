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
Linearity is `HopfAlgebra.IsLinear`, which lives in
`FormalConjecturesForMathlib/RingTheory/HopfAlgebra/Linear.lean` together with the multiplicative
matrices that express a homomorphism into `GLₙ`, and with lemmas exercising both.

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

open HopfAlgebra

universe u v

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
