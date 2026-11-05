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
# C*-selfless but non-C*-exact finitely generated groups

*Reference:* [Lacunary hyperbolic groups with fast injectivity radius growth and enough
loxodromic elements are selfless](https://arxiv.org/abs/2606.20456v1) by
*Goulnara Arzhantseva, Martin Finn-Sell* (2026).

A $C^*$-algebra $A$ is called **$C^*$-selfless** if it satisfies a quantitative strengthening
of the mixed-identity-free (MIF) property, introduced by
Amrutam–Gao–Kunnawalkam Elayavalli–Patchell.

A $C^*$-algebra $A$ is called **$C^*$-exact** if tensoring short exact sequences of
$C^*$-algebras with $A$ (using the spatial/minimal tensor product) preserves exactness.
Equivalently, $A$ embeds unitally into a nuclear $C^*$-algebra.

Conjecture 5.4 asks whether $C^*$-selflessness can coexist with failure of $C^*$-exactness.
The paper identifies Gromov monster groups (constructed via geometric small cancellation over
expander graphs) as candidate examples: they are known to be non-$C^*$-exact, and the paper
shows they are selfless under appropriate parameter choices. The missing step is establishing
the rapid decay property for these groups, which would promote selflessness to
$C^*$-selflessness.
-/

namespace Arxiv.«2606.20456»

/-
## Stub definitions

The following structures and predicates are not yet available in Mathlib. They are introduced
here as opaque constants sufficient to state Conjecture 5.4.
-/

/--
The **reduced group $C^*$-algebra** $C^*_r(G)$ of a discrete group $G$, defined as the
operator-norm closure of the group algebra $\mathbb{C}[G]$ acting on $\ell^2(G)$ by left
convolution. Not yet in Mathlib.
-/
opaque ReducedGroupCStarAlg (G : Type*) [Group G] : Type*

/--
A $C^*$-algebra is **$C^*$-exact** if tensoring any short exact sequence of $C^*$-algebras
with $A$ via the spatial tensor product again yields a short exact sequence. Equivalently,
$A$ embeds into a nuclear $C^*$-algebra. Not yet in Mathlib.
-/
opaque IsCStarExact (A : Type*) : Prop

/--
A $C^*$-algebra $A$ is **$C^*$-selfless** if it satisfies the quantitative strengthening of
the mixed-identity-free (MIF) property introduced by
Amrutam–Gao–Kunnawalkam Elayavalli–Patchell. Selflessness implies that the algebra has no
non-trivial "self-similar" subalgebras in a precise quantitative sense. Not yet in Mathlib.
-/
opaque IsCStarSelfless (A : Type*) : Prop

/--
**Conjecture 5.4 (Arzhantseva–Finn-Sell, 2026).** There exists a finitely generated group $G$
whose reduced $C^*$-algebra $C^*_r(G)$ is $C^*$-selfless but not $C^*$-exact.

If true, this would provide the first known example of a non-exact $C^*$-algebra with strict
comparison, connecting geometric group theory (via Gromov monster groups and the rapid decay
property) with the structure theory of operator algebras.
-/
@[category research open, AMS 20 46]
theorem exists_cstar_selfless_not_exact :
    ∃ (G : Type) (_ : Group G) (_ : Monoid.FG G),
      IsCStarSelfless (ReducedGroupCStarAlg G) ∧
      ¬ IsCStarExact (ReducedGroupCStarAlg G) := by
  sorry

end Arxiv.«2606.20456»
