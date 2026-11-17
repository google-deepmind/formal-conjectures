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
# Conjecture 20.15
by G.M.Bergman
*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v50)
!-/

@[expose] public section
namespace Kourovka.«20.15»
-- define the residually finite group G


/--
A group $G$ is residually finite if for every element $g$ that is not the identity in $G$ there is a homomorphism $\phi$ from $G$ to a finite group, such that $\phi(g) ≠ 1$.
-/
class ResiduallyFinite (G : Type*) extends Group G where
  fin_sep_one (g : G) : g ≠ 1 → ∃ F : FiniteGrp.{u_1}, ∃ (φ : G →* F), φ g ≠ 1

/--
Let $\kappa$ be an infinite cardinal. If residually finite group $G$ is embeddable in the full permutation group of a set of cardinality $\kappa$, must it be embeddable in the direct product of $\kappa$ finite groups?

The converse is true: any such direct product is residually finite and embeddable in the indicated permutation group. Also, the statement asked for becomes true if one replaces "direct product of 2^\kappa finite groups", since $G$ has cardinality at most $2^\kappa$, hence homomorphisms to that many finite groups can be chosen which, together, separate each element of $G$ from $e$.

See (G.M. Bergman, Indag. Math., 18 (2007), 349-403)
-/
@[category research open, question, AMS 20]
theorem kourovka_20_15 : ∀ (G : Type*) (s : Type), [Group G] → Infinite s → ResiduallyFinite G
    → (∃ f : G →* Equiv.Perm s, Function.Injective f) →
    ∃ H : s → FiniteGrp, ∃ ψ : G →* Π ι, H ι, Function.Injective ψ := by sorry


end Kourovka.«20.15»
