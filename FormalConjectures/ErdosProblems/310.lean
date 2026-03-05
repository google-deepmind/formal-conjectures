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
# Erdős Problem 310

*Reference:* [erdosproblems.com/310](https://www.erdosproblems.com/310)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Bl21] Bloom, T., *On a density conjecture about unit fractions* (2021).

[LiSa24] Liu, J. and Sawhney, M., *On a conjecture of Erdős on unit fractions* (2024).
-/

open Finset BigOperators

namespace Erdos310

/--
Let $\alpha > 0$ and $N \geq 1$. For any $A \subseteq \{1, \ldots, N\}$ with
$|A| \geq \alpha N$, there exists some $S \subseteq A$ such that
$\sum_{n \in S} 1/n = a/b$ with $a \leq b = O_\alpha(1)$.

That is, for every $\alpha > 0$ there exists a constant $C$ (depending only on $\alpha$) such
that for every $N \geq 1$ and every $A \subseteq \{1, \ldots, N\}$ with $|A| \geq \alpha N$,
there exist positive integers $a \leq b \leq C$ and a nonempty subset $S \subseteq A$ with
$\sum_{n \in S} 1/n = a/b$.

Liu and Sawhney [LiSa24] observed that the main result of Bloom [Bl21] implies
a positive solution to this conjecture. They proved the more precise bound
$b \leq \exp(O(1/\alpha))$, which they showed to be sharp.
-/
@[category research solved, AMS 5 11]
theorem erdos_310 :
    ∀ α : ℝ, α > 0 →
      ∃ C : ℕ, 0 < C ∧
        ∀ N : ℕ, 1 ≤ N →
          ∀ A : Finset ℕ, (∀ n ∈ A, 1 ≤ n ∧ n ≤ N) →
            α * (N : ℝ) ≤ (A.card : ℝ) →
              ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧
                ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ C ∧
                  ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (a : ℚ) / (b : ℚ) := by
  sorry

end Erdos310
