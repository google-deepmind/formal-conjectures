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
# Erdős Problem 540

Is it true that if $A \subseteq \mathbb{Z}/N\mathbb{Z}$ has size $\gg N^{1/2}$ then there exists
some non-empty $S \subseteq A$ such that $\sum_{n \in S} n \equiv 0 \pmod{N}$?

*Reference:* [erdosproblems.com/540](https://www.erdosproblems.com/540)

[Ol68] Olson, J. E., *A combinatorial problem on finite Abelian groups, I*, J. Number Theory (1968).

[Sz70] Szemerédi, E., *On a conjecture of Erdős and Heilbronn*, Acta Arith. (1970).

[Ba12] Balandraud, É., *An addition theorem and maximal zero-sum free sets in $\mathbb{Z}/p\mathbb{Z}$*,
Israel J. Math. (2012).
-/

open Finset BigOperators

namespace Erdos540

/--
Erdős Problem 540 (Erdős–Heilbronn conjecture):

Is it true that if $A \subseteq \mathbb{Z}/N\mathbb{Z}$ has size $\gg N^{1/2}$ then there exists
some non-empty $S \subseteq A$ such that $\sum_{n \in S} n \equiv 0 \pmod{N}$?

The answer is yes. This was proved for $N$ prime by Olson [Ol68], and for all $N$ by
Szemerédi [Sz70] (in fact for arbitrary finite abelian groups).

Erdős speculated that the correct threshold is $(2N)^{1/2}$; this was proved for $N$ prime
by Balandraud [Ba12].
-/
@[category research solved, AMS 5 11]
theorem erdos_540 : answer(True) ↔
    ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ), 0 < N →
    ∀ (A : Finset (ZMod N)),
      (A.card : ℝ) ≥ C * Real.sqrt (N : ℝ) →
      ∃ S : Finset (ZMod N), S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, n) = 0 := by
  sorry

end Erdos540
