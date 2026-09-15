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
# The Erdős–Ulam problem

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Ulam_problem)
* [Ul60] Ulam, S. M. (1960). *A Collection of Mathematical Problems.* Interscience, p. 40.
* [So19] Solymosi, J. and de Zeeuw, F. (2010). "On a question of Erdős and Ulam."
  *Discrete Comput. Geom.* 43, pp. 393--401. [arXiv:0806.3095](https://arxiv.org/abs/0806.3095)
* [Ta14] Tao, T. (2014). "The Erdős–Ulam problem, varieties of general type, and the
  Bombieri–Lang conjecture." Blog post,
  [terrytao.wordpress.com](https://terrytao.wordpress.com/2014/12/20/the-erdos-ulam-problem-varieties-of-general-type-and-the-bombieri-lang-conjecture/)
* [AH59] Anning, N. H. and Erdős, P. (1945). "Integral distances." *Bull. Amer. Math. Soc.* 51,
  pp. 598--600.
-/

open EuclideanSpace

namespace ErdosUlamProblem

/-- A set of points of the plane has **pairwise rational distances** if the distance between any
two of its points is a rational number. -/
def PairwiseRationalDistances (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, dist p q = (r : ℝ)

/--
**The Erdős–Ulam problem (Ulam 1945).**

Is there a dense subset of the plane whose points are at pairwise rational distances?
Conjecturally, no such set exists. Solymosi and de Zeeuw [So19] proved that a rational-distance
set is either finite or dense in a line or circle up to finitely many points; Tao [Ta14] and
Shaffaf showed that the Bombieri–Lang conjecture implies a negative answer.
-/
@[category research open, AMS 51 52]
theorem erdos_ulam_problem : answer(sorry) ↔
    ∃ S : Set (EuclideanSpace ℝ (Fin 2)), Dense S ∧ PairwiseRationalDistances S := by
  sorry

/--
**Everywhere-dense rational-distance sets on the line exist.**

On the real line the rationals themselves are dense and at pairwise rational distances; the
Erdős–Ulam problem is what happens in dimension `2`.
-/
@[category test, AMS 51 52]
theorem erdos_ulam_problem.variants.line :
    ∃ S : Set ℝ, Dense S ∧ ∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, dist p q = (r : ℝ) := by
  refine ⟨Set.range ((↑) : ℚ → ℝ), Rat.denseRange_cast, ?_⟩
  rintro p ⟨a, rfl⟩ q ⟨b, rfl⟩
  exact ⟨|a - b|, by rw [Real.dist_eq]; push_cast; rfl⟩

/--
**Infinite rational-distance sets are collinear or bounded in structure (Anning–Erdős 1945).**

Anning and Erdős proved that an infinite set of points in the plane with pairwise *integer*
distances must be contained in a line.

*Reference:* [AH59].
-/
@[category research solved, AMS 51 52]
theorem erdos_ulam_problem.variants.anning_erdos
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hinf : S.Infinite)
    (hd : ∀ p ∈ S, ∀ q ∈ S, ∃ n : ℤ, dist p q = (n : ℝ)) :
    ∃ a b : EuclideanSpace ℝ (Fin 2), a ≠ b ∧
      S ⊆ {x | ∃ t : ℝ, x = a + t • (b - a)} := by
  sorry

/--
**No dense rational-distance set is contained in a line or circle together with finitely many
extra points (Solymosi–de Zeeuw 2010).**

Every infinite plane set with pairwise rational distances has all but at most four of its
points on a line, or all but at most three of its points on a circle. In particular such a set
is never dense in the plane if the Bombieri–Lang-independent part is applied; here we state
the line-or-circle structure theorem.

*Reference:* [So19].
-/
@[category research solved, AMS 51 52]
theorem erdos_ulam_problem.variants.solymosi_de_zeeuw
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hinf : S.Infinite)
    (hd : PairwiseRationalDistances S) :
    (∃ a b : EuclideanSpace ℝ (Fin 2), a ≠ b ∧
        {x ∈ S | ¬ ∃ t : ℝ, x = a + t • (b - a)}.Finite) ∨
    (∃ (c : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), 0 < ρ ∧
        {x ∈ S | dist x c ≠ ρ}.Finite) := by
  sorry

end ErdosUlamProblem
