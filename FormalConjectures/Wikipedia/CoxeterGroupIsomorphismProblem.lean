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

/-!
# The Isomorphism Problem for Coxeter Groups

The *isomorphism problem for Coxeter groups* asks whether, given two Coxeter matrices
$M_1$ and $M_2$ (over finite index sets), one can determine if the corresponding Coxeter groups
$W(M_1)$ and $W(M_2)$ are isomorphic as abstract groups.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Isomorphism_problem_of_Coxeter_groups)
- B. Mühlherr, [*The isomorphism problem for Coxeter groups*](https://arxiv.org/abs/math/0506572), 2005.
-/

namespace IsomorphismProblemCoxeterGroups

open CoxeterMatrix CoxeterSystem

/-! ### Decidability of the Isomorphism Problem -/

/-- **The Isomorphism Problem for Coxeter Groups (Decidability).**
Given two Coxeter matrices $M_1$ and $M_2$ over finite index types, it is decidable whether
the Coxeter groups $W(M_1)$ and $W(M_2)$ are isomorphic as abstract groups.

This is Problem 1 from Mühlherr's paper:
> *"Given two Coxeter matrices $M$ and $M'$, decide whether the groups $W(M)$ and $W(M')$
> are isomorphic."*

This formulation is *constructive*: `Decidable` requires an actual decision procedure. -/
@[category research open, AMS 20]
noncomputable def coxeterGroup_isomorphism_decidable (n m : ℕ) 
    (M₁ : CoxeterMatrix (Fin n))
    (M₂ : CoxeterMatrix (Fin m)) :
    Decidable (Nonempty (M₁.Group ≃* M₂.Group)) :=
  sorry

/-! ### Finding All Isomorphisms -/

/-- **The Isomorphism Problem for Coxeter Groups (Finding All Isomorphisms).**
Given two Coxeter matrices $M_1$ and $M_2$ over finite index types, the set of all group
isomorphisms from $W(M_1)$ onto $W(M_2)$ is countable.

This is Problem 2 from Mühlherr's paper:
> *"Given two Coxeter matrices $M$ and $M'$, find all isomorphisms from $W(M)$ onto $W(M')$."*

This formulation is *non-constructive*: `Countable` only asserts existence of an enumeration.
For a constructive version, see `coxeterGroup_isomorphisms_encodable`. -/
@[category research open, AMS 20]
theorem coxeterGroup_find_all_isomorphisms (n m : ℕ)
    (M₁ : CoxeterMatrix (Fin n))
    (M₂ : CoxeterMatrix (Fin m)) :
    Countable (M₁.Group ≃* M₂.Group) :=
  sorry

/-- **The Isomorphism Problem for Coxeter Groups (Finding All Isomorphisms, Constructive).**
Given two Coxeter matrices $M_1$ and $M_2$ over finite index types, there is a computable
encoding of all group isomorphisms from $W(M_1)$ onto $W(M_2)$.

This is Problem 2 from Mühlherr's paper:
> *"Given two Coxeter matrices $M$ and $M'$, find all isomorphisms from $W(M)$ onto $W(M')$."*

This formulation is *constructive*: `Encodable` provides actual `encode`/`decode` functions. -/
@[category research open, AMS 20]
noncomputable def coxeterGroup_isomorphisms_encodable (n m : ℕ)
    (M₁ : CoxeterMatrix (Fin n))
    (M₂ : CoxeterMatrix (Fin m)) :
    Encodable (M₁.Group ≃* M₂.Group) :=
  sorry

/-- The constructive formulation (`Encodable`) implies the non-constructive one (`Countable`). -/
@[category test, AMS 20]
theorem coxeterGroup_find_all_isomorphisms_of_encodable (n m : ℕ)
    (M₁ : CoxeterMatrix (Fin n))
    (M₂ : CoxeterMatrix (Fin m))
    (h : Encodable (M₁.Group ≃* M₂.Group)) :
    Countable (M₁.Group ≃* M₂.Group) :=
  @Encodable.countable _ h

end IsomorphismProblemCoxeterGroups
