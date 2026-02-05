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
$W(M_1)$ and $W(M_2)$ are isomorphic as abstract groups. Equivalently, the problem asks to
characterize, for a given Coxeter group $W$, all possible Coxeter generating sets $S \subseteq W$
such that $(W, S)$ is a Coxeter system.

We formalize both the decidability question and the equivalent characterization problem.
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

/-! ### Equivalent Formulation: Characterizing Coxeter Generating Sets -/

/-- A subset `S` of a group `W` is a *Coxeter generating set* if there exists a Coxeter matrix `M`
and a Coxeter system on `W` such that `S` is exactly the set of simple reflections.

In other words, `S` is a Coxeter generating set if `(W, S)` can be realized as a Coxeter system. -/
@[category API, AMS 20]
def IsCoxeterGeneratingSet {W : Type*} [Group W] (S : Set W) : Prop :=
  ∃ (B : Type*) (M : CoxeterMatrix B) (cs : CoxeterSystem M W), S = Set.range cs.simple

/-- **The Isomorphism Problem (Equivalent Formulation).**
For a given Coxeter group `W`, it is decidable whether a finite subset `S ⊆ W` is a
Coxeter generating set.

This is equivalent to the original isomorphism problem: determining whether two Coxeter
presentations give isomorphic groups is equivalent to determining whether a given subset
of a Coxeter group forms a valid Coxeter generating set.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Isomorphism_problem_of_Coxeter_groups),
which states: "Equivalently, the problem asks to determine, for a given Coxeter group $W$,
the possible subsets $S$ of $W$ that are Coxeter generating sets for $W$ (that is, for which
$(W, S)$ is a Coxeter system)." -/
@[category research open, AMS 20]
noncomputable def coxeterGeneratingSet_decidable {n : ℕ} 
    {M : CoxeterMatrix (Fin n)}
    (S : Finset M.Group) :
    Decidable (IsCoxeterGeneratingSet (S : Set M.Group)) :=
  sorry

end IsomorphismProblemCoxeterGroups
