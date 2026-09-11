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
# The Gorenstein Symmetry Conjecture

Let $R$ be a commutative Artinian ring and let $A$ be an Artin $R$-algebra, that is, an
$R$-algebra which is finitely generated as an $R$-module.

* The **Gorenstein Symmetry Conjecture**: the injective dimension of $A$ as left $A$-module
   is finite if and only if the injective dimension of $A$ as right $A$-module is finite.

An algebra with both dimensions finite is called *(Iwanaga-)Gorenstein*. For such an algebra, the
two dimensions are equal by a theorem of Zaks [Zak69].

The conjecture was stated in the more restrictive setup of finite-dimensional algebras over an
algebraically closed field in the introduction of [Hap91].

Auslander and Reiten [AR91] have shown that any algebra $A$ whose left and right finitistic
dimensions are both finite satisfies the Gorenstein symmetry conjecture.
In particular, the Little Finitistic Dimension Conjecture implies the Gorenstein Symmetry conjecture.

The conjecture is also known for classes of algebras for which the Little Finitistic Dimension
Conjecture is not decided. An algebra satisfies the *Auslander condition* if in a minimal
injective resolution $0 \to {}_A A \to I^0 \to I^1 \to \cdots$ one has
$\operatorname{pd} I^j \leq j$ for every $j$. Auslander and Reiten [AR94] have shown that such an
algebra satisfies the Gorenstein Symmetry Conjecture. Its two injective dimensions and its two
finitistic dimensions are all equal [HQ10], so its finitistic dimension is finite exactly when
the algebra is Gorenstein. Whether that always happens is an open conjecture of Auslander and
Reiten [Hua24].

*References:*

- [AR91] M. Auslander, I. Reiten, [*Applications of contravariantly finite subcategories*](https://doi.org/10.1016/0001-8708%2891%2990037-8),
  Adv. Math. 86 (1991), 111-152
- [AR94] M. Auslander, I. Reiten, [*k-Gorenstein algebras and syzygy modules*](https://doi.org/10.1016/0022-4049%2894%2990044-2),
  J. Pure Appl. Algebra 92 (1994), no. 1, 1-27
- [Hap91] D. Happel, [*On Gorenstein algebras*](https://doi.org/10.1007/978-3-0348-8658-1_16),
  in: Representation Theory of Finite Groups and Finite-Dimensional Algebras, Progress in
  Mathematics 95, Birkhäuser, Basel, 1991, 389-404
- [HQ10] Z. Huang, H. Qin, [*Homological behavior of Auslander's k-Gorenstein rings*](https://arxiv.org/abs/math/0409161),
  arXiv:math/0409161
- [Hua24] Z. Huang, [*Auslander-type conditions and weakly Gorenstein algebras*](https://arxiv.org/abs/2408.05468),
  arXiv:2408.05468
- [Zak69] A. Zaks, [*Injective dimension of semi-primary rings*](https://doi.org/10.1016/0021-8693%2869%2990007-6),
  J. Algebra 13 (1969), 73-86
-/

open CategoryTheory Abelian

universe u v

namespace GorensteinSymmetryConjecture

/- Let `R` be a commutative Artinian ring and `A` an `R`-algebra which is finitely generated as
an `R`-module. -/
variable {R : Type u} {A : Type v} [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

include R in
/--
The **Gorenstein Symmetry Conjecture**: $A$ has finite injective dimension as a left module over
itself if and only if it has finite injective dimension as a right module over itself.
-/
@[category research open, AMS 16 18]
theorem gorenstein_symmetry : injectiveDimension (ModuleCat.of A A) < ⊤ ↔
    injectiveDimension (ModuleCat.of Aᵐᵒᵖ A) < ⊤ := by
  sorry

/-- The module structure carried by `ModuleCat.of Aᵐᵒᵖ A` is given by the right regular module $A_A$. -/
@[category test, AMS 16 18]
theorem op_smul_eq_mul (a x : A) :
    (MulOpposite.op a) • (x : (ModuleCat.of Aᵐᵒᵖ A : ModuleCat Aᵐᵒᵖ)) = x * a :=
  rfl

end GorensteinSymmetryConjecture
