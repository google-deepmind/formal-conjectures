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
# The McKay conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/McKay_conjecture)
- [CaSp26] Cabanes, Marc and Späth, Britta, [The McKay conjecture on character
  degrees](https://annals.math.princeton.edu/2026/203-3/p05). Ann. of Math. (2) 203 (2026),
  no. 3, 933--1032.
- [CaSp24] Cabanes, Marc and Späth, Britta, [The McKay conjecture on character
  degrees](https://arxiv.org/abs/2410.20392). arXiv:2410.20392 (2024).
-/

namespace McKay

noncomputable section

open CategoryTheory

section IrrDef

variable (G : Type) [Group G] [Fintype G]

/-- `IrrCharIsoClass G` is the type of isomorphism classes of irreducible (simple)
finite-dimensional complex representations of `G`. This formalizes `Irr(G)`. -/
def IrrCharIsoClass :=
  ThinSkeleton (ObjectProperty.FullSubcategory (Simple : ObjectProperty (FDRep ℂ G)))

/-- The degree of an irreducible character, defined as the dimension of the underlying
representation. -/
def IrrCharIsoClass.degree : IrrCharIsoClass G → ℕ :=
  Quotient.lift
    (fun V : ObjectProperty.FullSubcategory (Simple : ObjectProperty (FDRep ℂ G)) =>
      Module.finrank ℂ V.obj)
    (fun _ _ ⟨h⟩ => LinearEquiv.finrank_eq
      (FDRep.isoToLinearEquiv
        ((ObjectProperty.ι (Simple : ObjectProperty (FDRep ℂ G))).mapIso h)))

end IrrDef

section IrrPPrime

variable (G : Type) [Group G] [Fintype G] (p : ℕ)

/-- `irrPPrime G p` is the set of isomorphism classes of irreducible complex characters
of `G` whose degree is not divisible by `p`. This formalizes `Irr_{p'}(G)`. -/
def irrPPrime : Set (IrrCharIsoClass G) :=
  { χ | ¬(p ∣ IrrCharIsoClass.degree G χ) }

end IrrPPrime

/-- **The McKay conjecture.** Let $p$ be a prime, $G$ a finite group, and $P$ a Sylow
$p$-subgroup of $G$. Then the number of irreducible complex characters of $G$ whose degree is
not divisible by $p$ equals the corresponding number for the normalizer $N_G(P)$.

Cabanes and Späth proved the conjecture in [CaSp26]. -/
@[category research solved, AMS 20]
theorem mckay_conjecture
    (p : ℕ) [Fact (Nat.Prime p)]
    (G : Type) [Group G] [Fintype G]
    (P : Sylow p G) :
    Nat.card (irrPPrime G p) =
      Nat.card (irrPPrime (Subgroup.normalizer (P : Set G)) p) := by
  sorry

end

end McKay
