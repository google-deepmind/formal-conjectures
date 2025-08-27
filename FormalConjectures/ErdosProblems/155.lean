/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 155

*Reference:* [erdosproblems.com/155](https://www.erdosproblems.com/155)
-/

open Filter

namespace Erdos155

/--
Let $F(N)$ be the size of the largest Sidon subset of $\{1, \dots, N\}$.
-/
noncomputable abbrev F := maxSidonSetSize

/--
Is it true that for every $k \geq 1$ we have
$$
F(N + k) \leq F(N) + 1
$$
for all sufficiently large $N$?
-/
@[category research open, AMS 5]
theorem erdos_155 :
    (∀ k ≥ 1, ∀ᶠ N in atTop, F (N + k) ≤ F N + 1) ↔ answer(sorry) := by
  sorry

-- TODO: This may even hold with $k \approx ε * N ^ (1 / 2)$.

end Erdos155
