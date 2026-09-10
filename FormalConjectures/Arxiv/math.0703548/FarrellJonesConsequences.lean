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
# Algebraic consequences of the Farrell–Jones conjecture

The assembly map in the Farrell–Jones conjecture is not yet available in Mathlib. This file
states two of its algebraic consequences using projective modules and matrices over group rings:
the vanishing of the reduced projective class group and the Bass conjecture for commutative
integral domains.

*Reference:*
- [BLR08] [arxiv/math.0703548](https://arxiv.org/abs/math/0703548)
  **On the Farrell–Jones Conjecture and its applications**
  by *Arthur Bartels, Wolfgang Lück, Holger Reich*, J. Topol. 1 (2008), 57–86.
-/

namespace Arxiv.«math.0703548»

open scoped Classical in
/--
The value at the conjugacy class of `g` of the universal trace of a matrix over `R[G]`.

For each diagonal entry, this sums the coefficients of the elements conjugate to `g`. If the
matrix is idempotent, these values give the Hattori–Stallings rank of the projective module
represented by the matrix.
-/
noncomputable def matrixHattoriStallingsTraceAt {R : Type*} [CommRing R] {G : Type*} [Group G]
    {n : Type*} [Fintype n] (A : Matrix n n (MonoidAlgebra R G)) (g : G) : R :=
  ∑ i, (A i i).coeff.sum fun h r ↦ if IsConj h g then r else 0

/--
**Vanishing of the reduced projective class group for integral group rings.**

If `G` is torsion-free, that is, if its only element of finite order is `1`, then every finitely
generated projective module over `ℤ[G]` is stably free. This is the stable-freeness form of the
vanishing of $\widetilde K_0(\mathbb{Z}[G])$, which is the conclusion of Theorem 0.2 (ii) of
[BLR08] for the regular ring $\mathbb{Z}$. That theorem assumes the K-theoretic Farrell–Jones
conjecture for `G` with coefficients in `ℤ`.
-/
@[category research open, AMS 16 19 20]
theorem projective_module_isStablyFree {G : Type*} [Group G] (hG : ∀ g : G, IsOfFinOrder g → g = 1)
    (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]
    [Module.Finite (MonoidAlgebra ℤ G) M] [Module.Projective (MonoidAlgebra ℤ G) M] :
    Module.IsStablyFree (MonoidAlgebra ℤ G) M := by
  sorry

/--
**Bass conjecture for commutative integral domains, in idempotent-matrix form.**

Let `A` be an idempotent matrix over `R[G]`. If the order of `g` is not invertible in `R`, then
the Hattori–Stallings trace of the projective module represented by `A` vanishes at the conjugacy
class of `g`. This includes every infinite-order `g`, whose `orderOf` is zero. This is
Conjecture 0.6 of [BLR08]. By Theorems 0.5 (ii) and 0.7 of [BLR08] it follows from the
Farrell–Jones conjecture with coefficients in every field of prime characteristic.
-/
@[category research open, AMS 16 19 20]
theorem bass_conjecture_integral_domain {R : Type*} [CommRing R] [IsDomain R] {G : Type*}
    [Group G] {n : Type*} [Fintype n] (A : Matrix n n (MonoidAlgebra R G))
    (hA : A * A = A) (g : G) (hg : ¬IsUnit (orderOf g : R)) :
    matrixHattoriStallingsTraceAt A g = 0 := by
  sorry

end Arxiv.«math.0703548»
