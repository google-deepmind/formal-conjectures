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
# Erdős Problem 869

*References:*
- [erdosproblems.com/869](https://www.erdosproblems.com/869)
- [ErNa88] Erdős, Paul and Nathanson, Melvyn B., *Partitions of bases into disjoint unions of
  bases*. J. Number Theory (1988), 1-9.
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*. Hardy-Ramanujan J. (1992),
  34-50.
- [La26] Larsen, D., *Three questions of Erdős–Nathanson on asymptotic bases of order 2*.
  [arXiv:2603.03472](https://arxiv.org/abs/2603.03472) (2026).
-/

namespace Erdos869

/--
If $A_1, A_2$ are disjoint additive bases of order $2$ (i.e. $A_i + A_i$ contains all large
integers) then must $A = A_1 \cup A_2$ contain a minimal additive basis of order $2$ (one such that
deleting any element creates infinitely many $n \notin A + A$)?

A question of Erdős and Nathanson [ErNa88, Er92c]. The answer is no: Larsen [La26] constructed
disjoint bases $A_1, A_2$ of order $2$ such that $A_1 \cup A_2$ contains no minimal basis of
order $2$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos869.lean#L3490"]
theorem erdos_869 : answer(False) ↔
    ∀ (A₁ A₂ : Set ℕ), Disjoint A₁ A₂ →
      A₁.IsAsymptoticAddBasisOfOrder 2 → A₂.IsAsymptoticAddBasisOfOrder 2 →
      ∃ D ⊆ A₁ ∪ A₂, D.IsAsymptoticAddBasisOfOrder 2 ∧
        ∀ d ∈ D, ¬ (D \ {d}).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

end Erdos869
