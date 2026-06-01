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
# Černý Conjecture

A **synchronizing word** (also called a reset word) for a deterministic finite automaton (DFA)
$M = (Q, \Sigma, \delta)$ is a word $w \in \Sigma^*$ such that reading $w$ from any state always
leads to the same single state — formally, $\exists p \in Q, \forall q \in Q, \delta^*(q, w) = p$.

A DFA is called **synchronizing** if it admits at least one synchronizing word.

The **Černý conjecture** asserts that every synchronizing DFA with $n$ states has a
synchronizing word of length at most $(n - 1)^2$. This bound is sharp: the family of Černý
automata $C_n$ witnesses it, requiring exactly $(n - 1)^2$ steps.

**Status:** Open. The best known upper bound is
$\left(\frac{7}{48} + \frac{2 \cdot 15625}{1597536}\right) n^3 + o(n^3) \approx 0.1654\,n^3$
(Shitov, 2019). The bound $(n - 1)^2$ has been verified for small $n$ and for special classes of
automata (e.g., Eulerian, aperiodic, cyclic automata).

We use Mathlib's `DFA α σ` (from `Mathlib.Computability.DFA`), together with the auxiliary
`DFA.IsSynchronizingWord` and `DFA.IsSynchronizing` predicates defined in
`FormalConjecturesForMathlib.Computability.DFA`.

*References:*
- [Wikipedia: Synchronizing word](https://en.wikipedia.org/wiki/Synchronizing_word)
- J. Černý, [*Poznámka k homogénnym experimentom s konečnými automatmi*](https://dml.cz/bitstream/handle/10338.dmlcz/126647/MathSlov_14-1964-3_2.pdf),
  Matematicko-fyzikálny časopis, Vol. 14 (1964), No. 3, 208--216.
- Y. Shitov, *An improvement to a recent upper bound for synchronizing words of finite automata*,
  J. Autom. Lang. Comb. Vol. 24 (2019), 367--373.
-/

open Filter

namespace CernyConjecture

/-- **Černý Conjecture**: Every synchronizing DFA with $n$ states admits a
synchronizing word of length at most $(n - 1)^2$.
-/
@[category research open, AMS 68]
theorem cerny_conjecture :
    answer(sorry) ↔ ∀ {α : Type*} {σ : Type*} [Fintype σ] (M : DFA α σ) (hM : M.IsSynchronizing) ,
    ∃ w : List α, M.IsSynchronizingWord w ∧ w.length ≤ (Fintype.card σ - 1)^2 := by
  sorry

/-- **Shitov's bound (2019)**: Every synchronizing DFA with $n$ states admits a synchronizing
word of length at most $\left(\frac{7}{48} + \frac{2 \cdot 15625}{1597536}\right) n^3 + o(n^3)$,
where the $o(n^3)$ term is uniform over all alphabets. This is the best known upper bound
towards the Černý conjecture.
-/
@[category research solved, AMS 68]
theorem shitov_upper_bound :
    ∃ f : ℝ → ℝ, f =o[atTop] (fun n : ℝ => n ^ 3) ∧
    ∀ {α : Type*} {σ : Type*} [Fintype σ] (M : DFA α σ) (hM : M.IsSynchronizing) ,
    ∃ w : List α, M.IsSynchronizingWord w ∧
    (w.length : ℝ) ≤ (7 / 48 + 2 * 15625 / 1597536) * (Fintype.card σ : ℝ) ^ 3
      + f (Fintype.card σ : ℝ) := by
  sorry

end CernyConjecture
