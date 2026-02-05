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
-/

namespace IsomorphismProblemCoxeterGroups

open CoxeterMatrix CoxeterSystem

/-! ### Decidability of the Isomorphism Problem -/

/-- **The Isomorphism Problem for Coxeter Groups (Decidability).**
Given two Coxeter matrices $M_1$ and $M_2$ over finite index types, it is decidable whether
the Coxeter groups $W(M_1)$ and $W(M_2)$ are isomorphic as abstract groups.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Isomorphism_problem_of_Coxeter_groups),
which states: "Given two Coxeter groups $\Gamma_1$ and $\Gamma_2$, decide whether
$W(\Gamma_1) \simeq W(\Gamma_2)$." See also B. Mühlherr,
[*The isomorphism problem for Coxeter groups*](https://arxiv.org/abs/math/0506572), 2005. -/
@[category research open, AMS 20]
noncomputable def coxeterGroup_isomorphism_decidable (n m : ℕ) 
    (M₁ : CoxeterMatrix (Fin n))
    (M₂ : CoxeterMatrix (Fin m)) :
    Decidable (Nonempty (M₁.Group ≃* M₂.Group)) :=
  sorry

end IsomorphismProblemCoxeterGroups
