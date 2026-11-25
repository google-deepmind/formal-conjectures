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
module

public import FormalConjecturesUtil

/-!
# Existence of an extremal even unimodular lattice in dimension $96$

It is a fundamental problem in lattice theory to determine the dimensions
in which extremal even unimodular lattices can exist and to construct
explicit examples of them. Even unimodular lattices only exist in
dimensions divisible by $8$. Up to dimension $88$ it is known that
extremal even unimodular lattices exist for all such dimensions.

Is there an extremal even unimodular lattice in dimension $96$?
Here, extremal means every nonzero vector has squared norm at least
$10 = 2\lfloor 96/24 \rfloor + 2$.

*References:*
- [Sphere Packings, Lattices and Groups](https://doi.org/10.1007/978-1-4757-6568-7)
- [Two Extremal Even Unimodular Lattices of Rank $88$](https://arxiv.org/pdf/2609.15633)
- [Configurations of Extremal Even Unimodular Lattices](https://arxiv.org/pdf/0706.3082) - mentions the problem is open
- [On the degree-$2$ Siegel theta series of extremal even unimodular lattices of ranks $48$, $72$, $96$, and $120$](https://arxiv.org/pdf/2606.08733)
-/

@[expose] public section

open scoped InnerProductSpace

namespace Rank96ExtremalLattice

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-- A lattice is integral if all inner products of lattice vectors are integers. -/
def IsIntegralLattice (L : Submodule ℤ (E n)) : Prop :=
  ∀ (x y : L), ∃ k : ℤ, ⟪(x : (E n)), (y : (E n))⟫_ℝ = k

/-- A lattice is even if all squared norms are even integers.

Integrality follows from evenness by polarization:
$\langle x, y \rangle = \bigl(\lVert x + y \rVert^2 - \lVert x \rVert^2 - \lVert y \rVert^2\bigr)/2$
-/
def IsEvenLattice (L : Submodule ℤ (E n)) : Prop :=
  ∀ (x : L), ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k

/-- A unimodular lattice is an integral lattice whose fundamental domain has volume $1$. -/
def IsUnimodularLattice (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L] : Prop :=
  IsIntegralLattice L ∧ ZLattice.covolume L = 1

/--
By a theorem of Siegel, the minimal (squared) norm of an even unimodular
lattice in dimension $n$ is at most $2\lfloor n/24 \rfloor + 2$. Such a lattice is
extremal if equality is attained [Sphere Packings, Lattices and Groups, p. 194]. Equivalently, all
nonzero vectors have squared norm at least $2\lfloor n/24 \rfloor + 2$.

Does there exist an extremal even unimodular lattice in dimension $96$?
-/
@[category research open, question, AMS 11 52]
theorem exists_rank_96_extremal_lattice :
    ∃ (L : Submodule ℤ (E 96)) (_ : DiscreteTopology L) (_ : IsZLattice ℝ L),
    (∀ (x : L), x ≠ 0 → 10 ≤ ‖x‖ ^ 2) ∧
    IsEvenLattice L ∧ IsUnimodularLattice L := by
  sorry

end Rank96ExtremalLattice
