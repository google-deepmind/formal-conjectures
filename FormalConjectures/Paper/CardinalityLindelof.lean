/-
Copyright 2025 The Formal Conjectures Authors.

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
# Casas-Alvero Conjecture

*Reference:*
* [Selected Old Open Problems in General Topology](https://www.math.md/files/basm/y2013-n2-3/y2013-n2-3-(pp37-46).pdf.pdf) by
* [MathOverflow](https://mathoverflow.net/questions/27851)

The Casas-Alvero conjecture states that if a univariate polynomial `P` of degree `d` over a field
of characteristic zero shares a non-trivial factor with its Hasse derivatives up to order `d-1`,
then `P` must be of the form `(X - α)ᵈ` for some `α` in the field.

The conjecture has been proven for:
* Degrees `d ≤ 8`
* Degrees of the form `p^k` where `p` is prime
* Degrees of the form `2p^k` where `p` is prime

The conjecture is false in positive characteristic `p` for polynomials of degree `p+1`.

The conjecture is now claimed to be proven in this paper:
* [Proof of the Casas-Alvero conjecture: Soham Ghosh)](https://arxiv.org/pdf/2501.09272)

-/

open Cardinal

namespace CardinalityLindelof

variable (X : Type*) [TopologicalSpace X]
/--
A space where all singletons are Gδ points
-/
class HasPointsGδ : Prop where
  gδPoints : ∀ ⦃x : X⦄, IsGδ {x}

/-- Singletons are Gδ in First-Countable T₁ Spaces -/
instance HasPointsGδ.ofT1SpaceFirstCountable
    [FirstCountableTopology X] [T1Space X] : HasPointsGδ X where
  gδPoints := fun x ↦ IsGδ.singleton x


/--
Does every Lindelöf space with Gδ points have cardinality less or equal to the continuum?
-/
@[category research open, AMS 54]
theorem HasPointsGδ.lindelof_card :
    ∃ (X : Type*) (_ : TopologicalSpace X) (_ : HasPointsGδ X) (_ : LindelofSpace X), #X ≤ ℵ₀ := by
  sorry

--TODO under additional set theory axioms, there exists such a space with ℵ₀ < #X

end CardinalityLindelof
