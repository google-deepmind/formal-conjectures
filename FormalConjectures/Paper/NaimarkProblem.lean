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
# Naimark's problem

All nonzero irreducible representations of the C*-algebra `K(H)` of compact operators on a
Hilbert space `H` are unitarily equivalent. Naimark asked whether this property characterises
the algebras `K(H)` [Na51]. Rosenberg proved that it does for separable C*-algebras [Ro53].
Akemann and Weaver constructed a counterexample assuming Jensen's diamond principle [AW04], and
Calderón and Farah weakened the set-theoretic assumption [CF23]. Tanaka gave a counterexample in
ZFC [Ta26], and OpenAI gave another, with a Lean formalization [OAI26].

*References:*
- [AW04] C. Akemann and N. Weaver, *Consistency of a counterexample to Naimark's problem*,
  Proc. Natl. Acad. Sci. USA 101 (2004), 7522–7525.
- [CF23] D. Calderón and I. Farah, *Can you take Akemann–Weaver's `◇_{ℵ₁}` away?*, J. Funct.
  Anal. 285 (2023), 110017.
- [Na51] M. A. Naimark, *On a problem of the theory of rings with involution*, Uspekhi Mat. Nauk
  6 (1951), no. 6, 160–164.
- [Ro53] A. Rosenberg, *The number of irreducible representations of simple rings with no
  minimal ideals*, Amer. J. Math. 75 (1953), 523–530.
- [Ta26] R. Tanaka, *A separably representable counterexample to Naimark's problem in ZFC*,
  arXiv:2609.26930 (2026).
- [OAI26] OpenAI, *A counterexample to Naimark's problem in ZFC*. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf
-/

@[expose] public section

namespace NaimarkProblem

universe u v w

section Defs

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- `A` is a simple C*-algebra: it is nontrivial and has no closed two-sided ideals other than
`⊥` and `⊤`. -/
def IsSimpleCStar (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  Nontrivial A ∧ ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

/-- `f` is a state: a functional of norm one that is nonnegative on `star a * a`. -/
def IsState (f : A →L[ℂ] ℂ) : Prop :=
  ‖f‖ = 1 ∧ ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re

/-- `f` is a faithful tracial state. -/
def IsFaithfulTracialState (f : A →L[ℂ] ℂ) : Prop :=
  IsState f ∧ (∀ a b : A, f (a * b) = f (b * a)) ∧
    ∀ a : A, a ≠ 0 → 0 < (f (star a * a)).re

/-- A representation `π` of `A` on `H` is irreducible: it is nonzero and has no closed invariant
subspaces other than `⊥` and `⊤`. -/
def IsIrreducible {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  π ≠ 0 ∧ ∀ M : Submodule ℂ H, IsClosed (M : Set H) →
    (∀ a : A, ∀ x ∈ M, π a x ∈ M) → M = ⊥ ∨ M = ⊤

/-- Two representations are unitarily equivalent: a unitary `U : H → K` intertwines them. -/
def UnitarilyEquivalent {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] K, ∀ a : A, ∀ x : H, U (π a x) = ρ a (U x)

/-- Any two irreducible representations of `A`, on Hilbert spaces in the universes `v` and `w`,
are unitarily equivalent. -/
def HasUniqueIrreducibleRepresentation (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
    IsIrreducible π → IsIrreducible ρ → UnitarilyEquivalent π ρ

/-- `A` is isomorphic to the algebra of compact operators on `H`: some injective
*-homomorphism `A → B(H)` has image exactly the compact operators. -/
def IsIsomorphicToCompacts (A : Type*) [NonUnitalCStarAlgebra A]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∃ φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H), Function.Injective φ ∧
    ∀ T : H →L[ℂ] H, (∃ a : A, φ a = T) ↔ IsCompactOperator T

end Defs

/--
**Naimark's problem has a negative answer.** Not every C*-algebra whose irreducible
representations are all unitarily equivalent is isomorphic to the compact operators on a Hilbert
space.

Here `A` and all Hilbert spaces live in the same universe `u`, which is large enough to contain
every irreducible representation of `A`. This was proved by Tanaka [Ta26], and independently by
an internal OpenAI model in September 2026 [OAI26].
-/
@[category research solved, AMS 46]
theorem naimark_problem : ¬ ∀ (A : Type u) [NonUnitalCStarAlgebra A],
    HasUniqueIrreducibleRepresentation.{u, u, u} A →
      ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H), IsIsomorphicToCompacts A H := by
  sorry

/-- **Rosenberg.** A separable C*-algebra whose irreducible representations are all unitarily
equivalent is isomorphic to the compact operators on a Hilbert space [Ro53]. -/
@[category research solved, AMS 46]
theorem naimark_problem.variants.separable : ∀ (A : Type u) [NonUnitalCStarAlgebra A]
    [TopologicalSpace.SeparableSpace A], HasUniqueIrreducibleRepresentation.{u, u, u} A →
      ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H), IsIsomorphicToCompacts A H := by
  sorry

/-- A unital, infinite-dimensional, simple counterexample with a faithful tracial state
[Ta26, OAI26]. -/
@[category research solved, AMS 46]
theorem naimark_problem.variants.tracial : ∃ (A : Type u) (_ : CStarAlgebra A),
    IsSimpleCStar A ∧ ¬ FiniteDimensional ℂ A ∧ (∃ τ : A →L[ℂ] ℂ, IsFaithfulTracialState τ) ∧
    HasUniqueIrreducibleRepresentation.{u, u, u} A ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ¬ IsIsomorphicToCompacts A H := by
  sorry

/-- The tracial counterexample answers Naimark's problem. -/
@[category test, AMS 46]
theorem naimark_problem_of_tracial (h : type_of% naimark_problem.variants.tracial.{u}) :
    type_of% naimark_problem.{u} := by
  obtain ⟨A, _, -, -, -, huniq, hnot⟩ := h
  intro H
  obtain ⟨K, _, _, _, hK⟩ := H A huniq
  exact hnot K hK

end NaimarkProblem
