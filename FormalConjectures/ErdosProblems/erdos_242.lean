/-
Copyright 2025 Google LLC

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

-- Erdos Problems URL: https://www.erdosproblems.com/242
import FormalConjectures.Util.ProblemImports

open scoped Topology

/--
For every $n>2$ there exist distinct integers $1 ≤ x < y < z$
such that $4/n=1/x+1/y+1/z$.
-/
@[problem_status open]
theorem erdos_242 (n : ℕ) (hn : 2 < n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  sorry

/--
For any fixed $a$, if $n$ is sufficiently large in terms of $a$
then there exist distinct integers $1 ≤ x < y < z$ such that
a/n=1/x+1/y+1/z$.
-/
@[problem_status open]
theorem erdos_242_schinzel_generalization
    (a : ℕ) (ha : 0 < a) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  sorry
