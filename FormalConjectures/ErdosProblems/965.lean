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
# Erdős Problem 965

For every 2-coloring of ℝ, is there an uncountable set $A ⊆ ℝ$ such that
all sums $a + b$ for $a, b ∈ A, a ≠ b$ have the same colour?

*References:*
- [erdosproblems.com/965](https://www.erdosproblems.com/965)
- [Er75b] Erdős, Paul, Problems and results in combinatorial number theory. Journées Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295-310.
- [HLS17] Hindman, Neil and Leader, Imre and Strauss, Dona, Pairwise sums in colourings of the reals. Abh. Math. Semin. Univ. Hambg. (2017), 275--287.
- [Ko16] Komjáth, Péter, A certain 2-coloring of the reals. Real Anal. Exchange (2016), 227--231.
- [SWCol] Sokoup Dániel and Weiss, William, Sums and Anti-Ramsey Colourings of ℝ. https://danieltsoukup.github.io/academic/finset_colouring.pdf
-/

namespace Erdos965

/--
Erdős asks in [Er75b] if for every 2-coloring of ℝ, there is an uncountable set $A ⊆ ℝ$ such that
all sums $a + b$ for $a, b ∈ A, a ≠ b$ have the same colour.

In [Ko16] Péter Komjáth constructed a counterexample.
The same result was proven independently in [SWCol] by Sokoup and Weiss.
-/
@[category research solved, AMS 03 05]
theorem erdos_965 :
    answer(False) ↔ ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧
      ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A), a ≠ b → c ≠ d → f (a + b) = f (c + d) := by
  sorry

/--
In fact, in both [Ko16] and [SWCol] a generalized example for $k$-sums is constructed.
-/
@[category research solved, AMS 03 05]
theorem erdos_965.generalization : answer(False) ↔
     ∀ᵉ (k ≥ 2), ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧ ∀ s t : Finset ℝ,
      ↑s ⊆ A → ↑t ⊆ A → s.card = k → t.card = k → f (s.sum id) = f (t.sum id) := by
  sorry

end Erdos965
