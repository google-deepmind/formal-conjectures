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
# Erdős Problem 966

*Reference:* [erdosproblems.com/966](https://www.erdosproblems.com/966)

Let $k, r \geq 2$. Does there exist a set $A \subseteq \mathbb{N}$ that contains no non-trivial
arithmetic progression of length $k + 1$, yet in any $r$-colouring of $A$ there
must exist a monochromatic non-trivial arithmetic progression of length $k$?

A problem of Erdős [Er75b]. Spencer has shown that such a set exists.
This is an arithmetic analogue of the graph theory version [924].
-/

namespace Erdos966

/--
Erdős Problem 966 [Er75b]:

For all $k \geq 2$ and $r \geq 2$, there exists a set $A \subseteq \mathbb{N}$ that contains no
$(k+1)$-term arithmetic progression, yet every $r$-colouring of $A$ contains
a monochromatic $k$-term arithmetic progression.

Proved by Spencer.
-/
@[category research solved, AMS 5]
theorem erdos_966 : answer(True) ↔
    ∀ (k : ℕ) (r : ℕ), k ≥ 2 → r ≥ 2 →
      ∃ (A : Set ℕ),
        (¬∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k + 1 → a + i * d ∈ A) ∧
        (∀ c : ℕ → Fin r,
          ∃ a d : ℕ, 0 < d ∧
            (∀ i : ℕ, i < k → a + i * d ∈ A) ∧
            ∀ i : ℕ, i < k → c (a + i * d) = c a) := by
  sorry

end Erdos966
