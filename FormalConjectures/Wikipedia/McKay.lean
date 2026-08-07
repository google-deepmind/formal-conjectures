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

import FormalConjectures.Util.ProblemImports

/-
# The McKay Conjecture (now Theorem)

We formalize the definitions of characters and irreducible characters of finite groups,
and state the McKay conjecture: for a finite group `G`, a prime `p`, and a Sylow
`p`-subgroup `P` of `G`, the number of irreducible complex characters of `G` with
degree coprime to `p` equals the corresponding number for the normalizer `N_G(P)`.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/McKay_conjecture)
 - [Informal Proof](https://arxiv.org/abs/2410.20392) by *Cabanes* & *Späth*,
 which proves the McKay conjecture.
 - [McKay conjecture](https://annals.math.princeton.edu/articles/22056)
!-/

namespace McKay

noncomputable section

open CategoryTheory Classical

universe u

section IrrDef

variable (G : Type) [Group G] [Fintype G]

/-- The setoid on simple (irreducible) `FDRep ℂ G` given by categorical isomorphism. -/
instance simpleRepIsoSetoid : Setoid { V : FDRep ℂ G // Simple V } where
  r := fun V W => Nonempty (V.1 ≅ W.1)
  iseqv :=
    ⟨fun _ => ⟨Iso.refl _⟩,
     fun ⟨h⟩ => ⟨h.symm⟩,
     fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩⟩

/-- `IrrCharIsoClass G` is the type of isomorphism classes of irreducible (simple)
finite-dimensional complex representations of `G`. This formalizes `Irr(G)`. -/
def IrrCharIsoClass := Quotient (simpleRepIsoSetoid G)

/-- The degree of an irreducible character, defined as the dimension of the underlying
representation. -/
def IrrCharIsoClass.degree : IrrCharIsoClass G → ℕ :=
  Quotient.lift
    (fun V : { V : FDRep ℂ G // Simple V } => Module.finrank ℂ V.1)
    (fun _ _ ⟨h⟩ => LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv h))

end IrrDef

section IrrPPrime

variable (G : Type) [Group G] [Fintype G] (p : ℕ)

/-- `IrrPPrime G p` is the set of isomorphism classes of irreducible complex characters
of `G` whose degree is not divisible by `p`. This formalizes `Irr_{p'}(G)`. -/
def IrrPPrime : Set (IrrCharIsoClass G) :=
  { χ | ¬(p ∣ IrrCharIsoClass.degree G χ) }

end IrrPPrime

/-- **The McKay Conjecture.** Let `p` be a prime,
`G` a finite group, and `P` a Sylow
`p`-subgroup of `G`. Then the number of irreducible complex characters of `G` with
degree not divisible by `p` equals the number of such characters of the normalizer
`N_G(P)`. -/
@[category research solved, AMS 20]
theorem mckay_conjecture
    (p : ℕ) [Fact (Nat.Prime p)]
    (G : Type) [Group G] [Fintype G]
    (P : Sylow p G) :
    Nat.card (IrrPPrime G p) =
      Nat.card (IrrPPrime ((P : Subgroup G).normalizer) p) := by
  sorry
