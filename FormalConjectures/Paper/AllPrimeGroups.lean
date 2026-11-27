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
# The finitely presented Burnside problem

Does there exist an infinite finitely presented periodic group? OpenAI gives
a positive answer in [OAI26, Theorem 1.1]. A group is periodic if every element
has finite order. Finite presentation means an ordinary presentation with
finitely many generators and relators.

*References:*
- [OAI26] OpenAI, *An infinite finitely presented periodic group*
  (23 September 2026), Theorem 1.1.
  https://github.com/openai/math/tree/main/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026
- OpenAI, `PeriodicGroup` challenge, `OAI.SourceBurnside.BurnsideStatement`.
  https://github.com/openai/math/blob/main/lean/ComparatorChallenges/PeriodicGroup.lean
- [Ki26] Kenta Kitamura, *Infinite finitely presented residually finite p-groups
  for every prime*, GitHub repository (2026).
  https://github.com/KitaKen1/all-prime-residually-finite-p-groups
-/

@[expose] public section

namespace AllPrimeGroupsFC

/-- There exists an infinite finitely presented periodic group
[OAI26, Theorem 1.1]. -/
@[category research solved, question, AMS 20,
    formal_proof using lean4 at "https://github.com/KitaKen1/all-prime-residually-finite-p-groups/blob/c1ce611712e5a7804ed5056ad60600ffc941186a/lean/FCSolution.lean#L9-L11"]
theorem finitely_presented_burnside_problem :
    ∃ (G : Type) (inst : Group G),
      Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
        (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) := by
  sorry

namespace variants

/-- Variant 1 adds residual finiteness to the periodic-group existence problem.
The answer is yes, as a consequence of [Ki26]. -/
@[category research solved, question, AMS 20,
    formal_proof using lean4 at "https://github.com/KitaKen1/all-prime-residually-finite-p-groups/blob/c1ce611712e5a7804ed5056ad60600ffc941186a/lean/FCSolution.lean#L15-L24"]
theorem finitely_presented_burnside_problem_residually_finite :
    ∃ (G : Type) (inst : Group G),
      Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
        (∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) ∧
        @Group.ResiduallyFinite G inst := by
  sorry

/-- Variant 2 asks for an infinite finitely presented residually finite
$p$-group for every prime $p$. The answer is yes [Ki26]. -/
@[category research solved, question, AMS 20,
    formal_proof using lean4 at "https://github.com/KitaKen1/all-prime-residually-finite-p-groups/blob/c1ce611712e5a7804ed5056ad60600ffc941186a/lean/FCSolution.lean#L26-L28"]
theorem finitely_presented_burnside_problem_all_primes :
    ∀ p : ℕ, p.Prime →
      ∃ (G : Type) (inst : Group G),
        Infinite G ∧ @Group.IsFinitelyPresented G inst ∧
          @Group.ResiduallyFinite G inst ∧ @IsPGroup p G inst := by
  sorry

end variants

end AllPrimeGroupsFC
