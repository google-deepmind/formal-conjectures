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
# Tarski's exponential function problem

Tarski proved that the first-order theory of the real ordered field
$(\mathbb{R}, +, \cdot, -, 0, 1, \le)$ is decidable, and asked whether the same holds for the
real exponential field $\mathbb{R}_{\exp} = (\mathbb{R}, +, \cdot, -, 0, 1, \le, \exp)$.
The problem is open. Macintyre and Wilkie proved that the theory of $\mathbb{R}_{\exp}$ is
decidable if the real version of Schanuel's conjecture holds.

Decidability of a theory is formalised in `FirstOrder.Language.Theory.IsDecidable`: the set of
consequences of the theory is computable, with respect to the Gödel numbering of sentences from
`FormalConjecturesForMathlib.ModelTheory.Encoding`. The theory in question is the complete
theory of $\mathbb{R}_{\exp}$, which contains every sentence true in $\mathbb{R}_{\exp}$, so
this is the same as asking for an algorithm deciding membership
(`FirstOrder.Language.Theory.isDecidable_completeTheory_iff`). The statements use the language
of ordered rings with the order symbol `≤` in place of `<`. Some sources state the problem for
$(\mathbb{R}, +, \cdot, \exp)$ instead. Since $<$, $\le$, $-$, $0$ and $1$ are definable
from $+$ and $\cdot$, all these structures are interdefinable, and the choice does not affect
decidability.

*References:*
- [Wikipedia, *Tarski's exponential function problem*](https://en.wikipedia.org/wiki/Tarski%27s_exponential_function_problem),
  listed in [Wikipedia, *List of unsolved problems in mathematics*](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Model_theory_and_formal_languages).
- A. Tarski, *A decision method for elementary algebra and geometry*, 2nd ed., University of
  California Press, Berkeley and Los Angeles, 1951.
- A. Macintyre, A. J. Wilkie, *On the decidability of the real exponential field*, in:
  P. Odifreddi (ed.), *Kreiseliana: about and around Georg Kreisel*, A K Peters, Wellesley, MA,
  1996, pp. 441–467.
- S. Kuhlmann, [*Model theory of the real exponential function*](https://encyclopediaofmath.org/wiki/Model_theory_of_the_real_exponential_function),
  Encyclopedia of Mathematics.
- A. Berarducci, F. Gallinaro, [*On the elementary theory of the real exponential field*](https://arxiv.org/abs/2603.08365),
  arXiv:2603.08365 (2026). Assuming Schanuel's conjecture, gives an axiomatisation of the
  theory of $\mathbb{R}_{\exp}$ and recovers the Macintyre–Wilkie decidability result.
-/

namespace TarskiExponentialFunctionProblem

open FirstOrder FirstOrder.Language

/-- For the complete theory of the real exponential field, deciding consequences is the same
as deciding membership, since the theory contains every sentence true in $\mathbb{R}_{\exp}$. -/
@[category test, AMS 3]
theorem isDecidable_iff_isRecursive :
    (Language.orderedExpField.completeTheory ℝ).IsDecidable ↔
      (Language.orderedExpField.completeTheory ℝ).IsRecursive :=
  Theory.isDecidable_completeTheory_iff ℝ

/--
**Tarski's theorem.** The first-order theory of the real ordered field
$(\mathbb{R}, +, \cdot, -, 0, 1, \le)$ is decidable.
-/
@[category research solved, AMS 3 12]
theorem isDecidable_completeTheory_real_orderedField :
    ((Language.ring.sum Language.order).completeTheory ℝ).IsDecidable := by
  sorry

/--
**Tarski's exponential function problem.** Is the first-order theory of the real exponential
field $\mathbb{R}_{\exp} = (\mathbb{R}, +, \cdot, -, 0, 1, \le, \exp)$ decidable?
-/
@[category research open, AMS 3 12]
theorem tarski_exponential_function_problem :
    answer(sorry) ↔ (Language.orderedExpField.completeTheory ℝ).IsDecidable := by
  sorry

/-- The real version of Schanuel's conjecture: if $x_1, \ldots, x_n$ are real numbers that are
linearly independent over $\mathbb{Q}$, then the field
$\mathbb{Q}(x_1, \ldots, x_n, e^{x_1}, \ldots, e^{x_n})$ has transcendence degree at least $n$
over $\mathbb{Q}$. -/
def RealSchanuelConjecture : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), LinearIndependent ℚ x →
    n ≤ Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range x ∪ Set.range (Real.exp ∘ x)))

/--
**Macintyre–Wilkie.** If the real version of Schanuel's conjecture holds, then the first-order
theory of the real exponential field is decidable.
-/
@[category research solved, AMS 3 11 12]
theorem isDecidable_completeTheory_realExp_of_realSchanuelConjecture
    (h : RealSchanuelConjecture) :
    (Language.orderedExpField.completeTheory ℝ).IsDecidable := by
  sorry

end TarskiExponentialFunctionProblem
