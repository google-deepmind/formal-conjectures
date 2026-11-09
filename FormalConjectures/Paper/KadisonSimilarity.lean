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
# Kadison's similarity problem

Is every bounded unital homomorphism from a unital C*-algebra into the bounded operators on a
Hilbert space similar to a *-homomorphism? Kadison asked this in 1955 [Ka55]. Haagerup solved
the case of representations with a cyclic vector [Ha83], and Bunce and Christensen solved the
case of nuclear C*-algebras [Bu81, Ch81].

*References:*
- [Bu81] J. W. Bunce, *The similarity problem for representations of C*-algebras*, Proc. Amer.
  Math. Soc. 81 (1981), 409–414.
- [Ch81] E. Christensen, *On non self-adjoint representations of C*-algebras*, Amer. J. Math.
  103 (1981), 817–833.
- [Ha83] U. Haagerup, *Solution of the similarity problem for cyclic representations of
  C*-algebras*, Ann. of Math. 118 (1983), 215–240.
- [Ka55] R. V. Kadison, *On the orthogonalization of operator representations*, Amer. J. Math.
  77 (1955), 600–620.
- [OAI26] OpenAI, *Kadison's similarity theorem through uniform derivation estimates*. OpenAI
  Math Release preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf
-/

@[expose] public section

namespace KadisonSimilarity

universe u v

section Defs

variable (A H : Type*) [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded unital representation of `A` on `H`: a continuous unital `ℂ`-algebra
homomorphism `A → B(H)`. Nothing is assumed about the star operation. -/
abbrev BoundedUnitalHom :=
  {π : A →ₐ[ℂ] (H →L[ℂ] H) // Continuous π}

/-- `π` is similar to a *-homomorphism: for some invertible `S ∈ B(H)`, the map
`a ↦ S π(a) S⁻¹` sends `star a` to the adjoint of the image of `a`. -/
def SimilarToStar (π : BoundedUnitalHom A H) : Prop :=
  ∃ S : (H →L[ℂ] H)ˣ, ∀ a : A,
    (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))

end Defs

/--
**Kadison's similarity problem.** Every bounded unital homomorphism from a unital C*-algebra
into the bounded operators on a complex Hilbert space is similar to a *-homomorphism.

This was proved by an internal OpenAI model in September 2026 [OAI26].
-/
@[category research solved, AMS 46 47]
theorem kadison_similarity : ∀ (A : Type u) [CStarAlgebra A] (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : BoundedUnitalHom A H), SimilarToStar A H π := by
  sorry

/-- **Haagerup.** A bounded unital homomorphism with a cyclic vector is similar to a
*-homomorphism [Ha83]. -/
@[category research solved, AMS 46 47]
theorem kadison_similarity.variants.cyclic : ∀ (A : Type u) [CStarAlgebra A] (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : BoundedUnitalHom A H), (∃ ξ : H, Dense (Set.range fun a => π.1 a ξ)) →
      SimilarToStar A H π := by
  sorry

/-- The commutative case. Commutative C*-algebras are nuclear, so this is a special case of the
theorem of Bunce and Christensen [Bu81, Ch81]. -/
@[category research solved, AMS 46 47]
theorem kadison_similarity.variants.commutative : ∀ (A : Type u) [CommCStarAlgebra A]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : BoundedUnitalHom A H), SimilarToStar A H π := by
  sorry

/-- Sanity check: a homomorphism that already preserves the star operation is similar to a
*-homomorphism, with `S = 1`. -/
@[category test, AMS 46 47]
theorem similarToStar_of_map_star {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : BoundedUnitalHom A H) (hπ : ∀ a, π.1 (star a) = star (π.1 a)) :
    SimilarToStar A H π :=
  ⟨1, fun a => by simp [hπ]⟩

/-- The general statement implies Haagerup's cyclic case. -/
@[category test, AMS 46 47]
theorem cyclic_of_kadison_similarity (h : type_of% kadison_similarity.{u, v}) :
    type_of% kadison_similarity.variants.cyclic.{u, v} :=
  fun A _ H _ _ _ π _ => h A H π

end KadisonSimilarity
