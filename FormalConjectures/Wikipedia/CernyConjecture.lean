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
# Černý Conjecture

A **synchronizing word** (also called a reset word) for a deterministic finite automaton (DFA)
`M = (Q, Σ, δ)` is a word `w ∈ Σ*` such that reading `w` from any state always leads to the
same single state — formally, `∃ p ∈ Q, ∀ q ∈ Q, δ*(q, w) = p`.

A DFA is called **synchronizing** if it admits at least one synchronizing word.

The **Černý conjecture** asserts that every synchronizing DFA with `n` states has a
synchronizing word of length at most `(n - 1)²`. This bound is sharp: the family of Černý
automata `Cₙ` witnesses it, requiring exactly `(n - 1)²` steps.

**Status:** Open. The best known upper bound is approximately `n(7n² + 6n − 16)/48`
(Shitov, 2019). The bound `(n − 1)²` has been verified for small `n` and for special classes of
automata (e.g., Eulerian, aperiodic, cyclic automata).

We use Mathlib's `DFA α σ` (from `Mathlib.Computability.DFA`), which consists of:
- a state type `σ`,
- an alphabet type `α`,
- a transition function `step : σ → α → σ`,
- a starting state `start : σ`,
- a set of accepting states `accept : Set σ`.

The key function is `M.evalFrom s w : σ`, which evaluates the word `w : List α` starting from
state `s`, using `List.foldl`.

*References:*
- [Wikipedia: Černý conjecture](https://en.wikipedia.org/wiki/Černý_conjecture)
- [Wikipedia: Synchronizing word](https://en.wikipedia.org/wiki/Synchronizing_word)
- J. Černý, *Poznámka k homogénnym experimentom s konečnými automatmi*, 1964.
-/

namespace CernyConjecture

variable {α : Type*} {σ : Type*}

/-! ## Core definitions -/

/-- A word `w` is a **synchronizing word** (or reset word) for a DFA `M` if reading `w` from
any state leads to the same single state. -/
def IsSynchronizingWord (M : DFA α σ) (w : List α) : Prop :=
  ∃ p : σ, ∀ q : σ, M.evalFrom q w = p

/-- A DFA `M` is **synchronizing** if it has at least one synchronizing word. -/
def IsSynchronizing (M : DFA α σ) : Prop :=
  ∃ w : List α, IsSynchronizingWord M w

/-! ## The conjecture -/

/-- **Černý Conjecture**: Every synchronizing DFA with `n` states admits a synchronizing word of
length at most `(n - 1)²`.
-/
@[category research open, AMS 68]
theorem cerny_conjecture [Fintype σ] (M : DFA α σ) (hM : IsSynchronizing M) :
    answer(sorry) ↔ ∃ w : List α, IsSynchronizingWord M w ∧ w.length ≤ (Fintype.card σ - 1)^2 := by
  sorry

end CernyConjecture
