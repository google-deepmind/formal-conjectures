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
# Auslander Conjecture in Homological Algebra
*Reference:*
We use the Artin-algebra formulation of the Auslander Conjecture following D.A. Jorgensen and L.M. Şega
[Nonvanishing cohomology and classes of Gorenstein rings](https://arxiv.org/abs/math/0306001).
Published as
[Adv. Math. 188 (2004), 470-490](https://doi.org/10.1016/j.aim.2003.11.003).
The Auslander Conjecture was disproved in this article.

Remarks:
D. Happel attributed a more restrictive formulation of the conjecture to Maurice Auslander in a lecture note from 1990
[Homological conjectures in representation theory of finite-dimensional algebras](https://www.math.uni-bielefeld.de/~sek/dim2/happel2.pdf).
In this lecture note, the conjecture was formulated for finite-dimensional algebras
over algebraically closed fields. The work of Jorgensen and Şega disproves this more restrictive formulation as well.

The counterexamples of Jorgensen and Şega are certain commutative local finite-dimensional algebras.

The Little Finitistic Dimension Conjecture for a finite-dimensional algebra $A$ over a field $k$
is valid if its enveloping algebra $A ⊗_k A^{op}$  satisfies the Auslander Conjecture. This observation is attributed to Auslander in Happel's lecture note.

The conjecture should not be confused with the Auslander Conjecture of Louis Auslander on affine
crystallographic groups.
-/

open CategoryTheory.Abelian

namespace Arxiv.«math.0306001»

/--
Auslander Conjecture (disproved):
Let $A$ be an Artin algebra over a commutative Artinian ring $R$.
For any finitely generated left $A$-module $X$ there is an integer $n ≥ 0$ such that
for any finitely generated left $A$-module $Y$ satisfying $\operatorname{Ext}^i_A(X,Y) = 0$ for $i ≫ 0$
it follows that $\operatorname{Ext}^i_A(X,Y) = 0$ for any $i ≥ n$.

AMS 16: Associative rings and algebras
AMS 18: Category theory; homological algebra
-/

@[category research solved, AMS 16 18]
theorem AuslanderConjecture :
  ¬ ∀ (R : Type*) (A : Type*)
    [CommRing R] [IsArtinianRing R]
    [Ring A] [Algebra R A] [Module.Finite R A],
      ∀ (X : ModuleCat A) [Module.Finite A X],
        ∃ n : ℕ,
          ∀ (Y : ModuleCat A) [Module.Finite A Y],
          (hY : ∃ m : ℕ, ∀ i : ℕ, m ≤ i → Subsingleton (Ext X Y i)) →
            ∀ i : ℕ, n ≤ i → Subsingleton (Ext X Y i) := by
  sorry

end Arxiv.«math.0306001»
