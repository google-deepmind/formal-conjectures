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
# Erdős Problem 532

*References:*
- [erdosproblems.com/532](https://www.erdosproblems.com/532)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of combinatorial theory (1973), 117-138.
- [Er75b] Erdős, Paul, *Problems and results in combinatorial number theory*. Journées Arithmétiques de Bordeaux (1975), 295-310.
- [Er77c] Erdős, Paul, *Problems and results on combinatorial number theory. III*. Number theory day (1977), 43-72.
- [Hi74] Hindman, Neil, *Finite sums from sequences within cells of a partition of $\mathbb{N}$*. J. Combinatorial Theory Ser. A (1974), 1-11.
-/

namespace Erdos532

/--
If $\mathbb{N}$ is 2-coloured then is there some infinite set $A\subseteq \mathbb{N}$ such that
all finite subset sums\[ \sum_{n\in S}n\](as $S$ ranges over all non-empty finite subsets of $A$)
are monochromatic?

Asked by Graham and Rothschild. Proved by Hindman [Hi74] (for any number of colours).
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos532.lean"]
theorem erdos_532 :
    answer(True) ↔ ∀ (c : ℕ → Fin 2),
      ∃ A : Set ℕ, A.Infinite ∧
        ∃ color : Fin 2,
          ∀ S : Finset ℕ, S.Nonempty → ↑S ⊆ A →
            c (∑ n ∈ S, n) = color := by
  sorry

end Erdos532
