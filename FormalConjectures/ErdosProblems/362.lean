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

[SaSz] Sárközy, A. and Szemerédi, E., on the number of subsets whose sum is equal to a given
number.

[Ha] Halász, G., on the number of subsets with given sum and cardinality.
-/

open Finset

namespace Erdos362

/--
Let $A \subseteq \mathbb{N}$ be a finite set of size $N$. For any fixed $t$, the number of
subsets $S \subseteq A$ with $\sum_{n \in S} n = t$ is $\ll 2^N / N^{3/2}$.

Proved by Sárközy and Szemerédi [SaSz], removing a log factor from the earlier
bound of Erdős and Moser.
-/
@[category research solved, AMS 5 11]
theorem erdos_362 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ), 0 < N →
    ∀ (A : Finset ℕ), A.card = N →
    ∀ (t : ℕ),
    ((A.powerset.filter (fun S => decide (S.sum id = t))).card : ℝ) ≤
      C * (2 : ℝ) ^ N / ((N : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry

/--
Let $A \subseteq \mathbb{N}$ be a finite set of size $N$. For any fixed $t$ and $l$, the number of
subsets $S \subseteq A$ with $\sum_{n \in S} n = t$ and $|S| = l$ is $\ll 2^N / N^2$,
with the implied constant independent of $l$ and $t$.

Proved by Halász [Ha] as a consequence of a more general multi-dimensional result.
-/
@[category research solved, AMS 5 11]
theorem erdos_362.variants.fixed_size :
    ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ), 0 < N →
    ∀ (A : Finset ℕ), A.card = N →
    ∀ (t l : ℕ),
    ((A.powerset.filter (fun S => decide (S.sum id = t ∧ S.card = l))).card : ℝ) ≤
      C * (2 : ℝ) ^ N / ((N : ℝ) ^ 2) := by
  sorry

end Erdos362
