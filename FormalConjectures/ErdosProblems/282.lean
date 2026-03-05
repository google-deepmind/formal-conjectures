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
# Erdős Problem 282

*Reference:* [erdosproblems.com/282](https://www.erdosproblems.com/282)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos282

/-- The greedy step: given a set $A \subseteq \mathbb{N}$ and a positive rational $x$,
    returns the minimal $n \in A$ such that $n \geq 1/x$. Returns $0$ if $x \leq 0$. -/
noncomputable def greedyDenominator (A : Set ℕ) (x : ℚ) : ℕ :=
  if x ≤ 0 then 0
  else sInf {n : ℕ | n ∈ A ∧ x⁻¹ ≤ (n : ℚ)}

/-- The greedy remainder sequence: starting from $x$, repeatedly subtract $1/n$
    where $n$ is chosen greedily as the minimal element of $A$ with $n \geq 1/x$. -/
noncomputable def greedyRemainder (A : Set ℕ) (x : ℚ) : ℕ → ℚ
  | 0 => x
  | k + 1 =>
    let r := greedyRemainder A x k
    if r ≤ 0 then 0
    else r - 1 / ↑(greedyDenominator A r)

/--
Erdős Problem 282 [ErGr80, p.30]:

The greedy algorithm for Egyptian fractions with odd denominators always
terminates: for every rational $x \in (0,1)$ with odd denominator, the process of
repeatedly choosing the minimal odd $n \geq 1/x$ and replacing $x$ by $x - 1/n$
terminates after finitely many steps.
-/
@[category research open, AMS 11]
theorem erdos_282 :
    answer(sorry) ↔
    ∀ x : ℚ, 0 < x → x < 1 → x.den % 2 = 1 →
    ∃ k : ℕ, greedyRemainder {n : ℕ | n % 2 = 1} x k = 0 := by
  sorry

end Erdos282
