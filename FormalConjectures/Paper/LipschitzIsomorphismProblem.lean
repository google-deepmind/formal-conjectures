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
# The Lipschitz isomorphism problem for separable Banach spaces

Two Banach spaces are *Lipschitz isomorphic* if there is a bijection between them that is
Lipschitz in both directions. Aharoni and Lindenstrauss constructed Lipschitz isomorphic
nonseparable Banach spaces that are not linearly isomorphic, and asked for separable
examples [AL78, pp. 281–282]. The separable question was left open in [JLS96, Section 8(3)].

*References:*
- [AL78] I. Aharoni and J. Lindenstrauss, *Uniform equivalence between Banach spaces*,
  Bull. Amer. Math. Soc. 84 (1978), 281–283.
- [JLS96] W. B. Johnson, J. Lindenstrauss and G. Schechtman, *Banach spaces determined by their
  uniform structures*, Geom. Funct. Anal. 6 (1996), 430–470.
- [OAI26] OpenAI, *Lipschitz equivalent separable Banach spaces need not be linearly
  isomorphic*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Lipschitz-Equivalent-Separable-Banach-Spaces-Need-Not-Be-Linearly-Isomorphic-September-24-2026/paper.pdf
-/

@[expose] public section

namespace LipschitzIsomorphismProblem

/--
**Lipschitz isomorphic separable Banach spaces need not be linearly isomorphic.** There are
separable real Banach spaces $X$ and $Y$ with a bijection $X \to Y$ that is Lipschitz in both
directions, but no linear isomorphism $X \to Y$.

This was proved by an internal OpenAI model in September 2026 [OAI26]. In that example $X$
contains a linearly isometric copy of $c_0(\ell_2)$ while $Y$ contains no closed subspace
linearly isomorphic to $c_0(\ell_2)$.
-/
@[category research solved, AMS 46]
theorem lipschitz_isomorphism_problem :
    ∃ (X Y : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (_ : CompleteSpace X)
      (_ : TopologicalSpace.SeparableSpace X) (_ : NormedAddCommGroup Y) (_ : NormedSpace ℝ Y)
      (_ : CompleteSpace Y) (_ : TopologicalSpace.SeparableSpace Y),
      (∃ (e : X ≃ Y) (K K' : NNReal), LipschitzWith K e ∧ LipschitzWith K' e.symm) ∧
        IsEmpty (X ≃L[ℝ] Y) := by
  sorry

/-- **Aharoni–Lindenstrauss.** Without separability there are Lipschitz isomorphic Banach
spaces that are not linearly isomorphic [AL78]. -/
@[category research solved, AMS 46]
theorem lipschitz_isomorphism_problem.variants.nonseparable :
    ∃ (X Y : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (_ : CompleteSpace X)
      (_ : NormedAddCommGroup Y) (_ : NormedSpace ℝ Y) (_ : CompleteSpace Y),
      (∃ (e : X ≃ Y) (K K' : NNReal), LipschitzWith K e ∧ LipschitzWith K' e.symm) ∧
        IsEmpty (X ≃L[ℝ] Y) := by
  sorry

/-- The separable statement implies the general one. -/
@[category test, AMS 46]
theorem nonseparable_of_lipschitz_isomorphism_problem
    (h : type_of% lipschitz_isomorphism_problem) :
    type_of% lipschitz_isomorphism_problem.variants.nonseparable := by
  obtain ⟨X, Y, _, _, _, -, _, _, _, -, he, hiso⟩ := h
  exact ⟨X, Y, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, he, hiso⟩

end LipschitzIsomorphismProblem
