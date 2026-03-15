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
# Erdős Problem 362

*Reference:* [erdosproblems.com/362](https://www.erdosproblems.com/362)

[Er65] Erdős, P., _Extremal problems in number theory_. Proc. Sympos. Pure Math. **VIII**
(1965), 181–189.

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo.,
1971) (1973), 117–138.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[SaSz65] Sárközy, A. and Szemerédi, E., _Über ein Problem von Erdős und Moser_. Acta
Arithmetica (1965), 205–208.

[Ha77] Halász, G., _Estimates for the concentration function of combinatorial number theory and
probability_. Periodica Mathematica Hungarica (1977), 197–211.
-/

open Finset

namespace Erdos362

/--
Let $A \subseteq \mathbb{N}$ be a finite set of size $N$. For any fixed $t$, the number of
subsets $S \subseteq A$ with $\sum_{n \in S} n = t$ is $\ll 2^N / N^{3/2}$.

Proved by Sárközy and Szemerédi [SaSz65], removing a log factor from the earlier
bound of Erdős and Moser [Er65].
-/
@[category research solved, AMS 5 11]
theorem erdos_362 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ), 0 < N →
    ∀ (A : Finset ℕ), A.card = N →
    ∀ (t : ℕ),
    ((A.powerset.filter (fun S => S.sum id = t)).card : ℝ) ≤
      C * (2 : ℝ) ^ N / ((N : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry

/--
Let $A \subseteq \mathbb{N}$ be a finite set of size $N$. For any fixed $t$ and $l$, the number of
subsets $S \subseteq A$ with $\sum_{n \in S} n = t$ and $|S| = l$ is $\ll 2^N / N^2$,
with the implied constant independent of $l$ and $t$.

Proved by Halász [Ha77] as a consequence of a more general multi-dimensional result.
-/
@[category research solved, AMS 5 11]
theorem erdos_362.variants.fixed_size :
    ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ), 0 < N →
    ∀ (A : Finset ℕ), A.card = N →
    ∀ (t l : ℕ),
    ((A.powerset.filter (fun S => S.sum id = t ∧ S.card = l)).card : ℝ) ≤
      C * (2 : ℝ) ^ N / ((N : ℝ) ^ 2) := by
  sorry

end Erdos362
