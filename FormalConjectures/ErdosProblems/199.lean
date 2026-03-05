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
# Erdős Problem 199

*Reference:* [erdosproblems.com/199](https://www.erdosproblems.com/199)

If $A \subset \mathbb{R}$ does not contain a 3-term arithmetic progression then must
$\mathbb{R} \setminus A$ contain an infinite arithmetic progression?

The answer is no, as shown by Baumgartner [Ba75] (whose construction uses
the axiom of choice to provide a basis for $\mathbb{R}$ over $\mathbb{Q}$).

[Er75b] Erdős, P.

[ErGr79] Erdős, P. and Graham, R.

[ErGr80] Erdős, P. and Graham, R.

[Ba75] Baumgartner, J.E.
-/

namespace Erdos199

/-- A set $A \subseteq \mathbb{R}$ contains a 3-term arithmetic progression if there exist
$a, d \in \mathbb{R}$ with $d \neq 0$ such that $a, a + d, a + 2d \in A$. -/
def HasThreeTermAP (A : Set ℝ) : Prop :=
  ∃ a d : ℝ, d ≠ 0 ∧ a ∈ A ∧ (a + d) ∈ A ∧ (a + 2 * d) ∈ A

/-- A set $S \subseteq \mathbb{R}$ contains an infinite arithmetic progression if there exist
$a, d \in \mathbb{R}$ with $d \neq 0$ such that $a + n \cdot d \in S$ for all $n : \mathbb{N}$. -/
def HasInfiniteAP (S : Set ℝ) : Prop :=
  ∃ a d : ℝ, d ≠ 0 ∧ ∀ n : ℕ, (a + ↑n * d) ∈ S

/--
Erdős Problem 199 [Er75b, ErGr79, ErGr80] (DISPROVED):

If $A \subset \mathbb{R}$ does not contain a 3-term arithmetic progression, must
$\mathbb{R} \setminus A$ contain an infinite arithmetic progression?

Baumgartner [Ba75] showed the answer is no, using the axiom of choice
to construct a counterexample via a Hamel basis for $\mathbb{R}$ over $\mathbb{Q}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_199 : answer(False) ↔ ∀ A : Set ℝ, ¬HasThreeTermAP A → HasInfiniteAP Aᶜ := by
  sorry

end Erdos199
