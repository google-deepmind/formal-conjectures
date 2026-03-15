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
# Erdős Problem 1027

*Reference:* [erdosproblems.com/1027](https://www.erdosproblems.com/1027)

Let $c > 0$, and let $n$ be sufficiently large depending on $c$. Suppose that $\mathcal{F}$ is a
family of at most $c \cdot 2^n$ many finite sets of size $n$. Let
$X = \bigcup_{A \in \mathcal{F}} A$.

Must there exist $\gg_c 2^{|X|}$ many sets $B \subset X$ which intersect every set in
$\mathcal{F}$, yet contain none of them?

Note: The existence of a single such set $B$ is equivalent to $\mathcal{F}$ having Property B
(see Problem 901). This problem asks for a quantitative strengthening.

This was proved in the affirmative by Koishi Chan, with contributions from Stijn Cambie.

[Er64e] Erdős, P., _On a combinatorial problem. II_. Acta Mathematica Academiae Scientiarum
Hungaricae **15** (1964), 445–447.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.
-/

open Finset

namespace Erdos1027

/--
Erdős Problem 1027:
For every $c > 0$, there exist $\delta > 0$ and $N_0$ such that for all $n \geq N_0$,
for any family $\mathcal{F}$ of finite sets each of size $n$ with
$|\mathcal{F}| \leq c \cdot 2^n$, letting $X = \bigcup \mathcal{F}$, the number of subsets
$B$ of $X$ that intersect every member of $\mathcal{F}$ but contain none of them is at least
$\delta \cdot 2^{|X|}$.
-/
@[category research solved, AMS 5]
theorem erdos_1027 :
    answer(True) ↔
    ∀ c : ℝ, c > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ F : Finset (Finset ℕ),
      (∀ A ∈ F, A.card = n) →
      (F.card : ℝ) ≤ c * (2 : ℝ) ^ n →
      let X := F.biUnion id
      ((X.powerset.filter (fun B =>
        (∀ A ∈ F, (A ∩ B).Nonempty) ∧
        (∀ A ∈ F, ¬(A ⊆ B)))).card : ℝ) ≥ δ * (2 : ℝ) ^ X.card := by
    sorry

end Erdos1027
