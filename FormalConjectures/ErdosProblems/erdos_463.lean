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

-- Erdos Problems URL: https://www.erdosproblems.com/463
import FormalConjectures.Util.ProblemImports

open Filter

/--
Is there a function $f$ with $f(n)\to\infty$ as $n\to\infty$ such that,
for all large $n$, there is a composite number $m$ such that
$$
n + f(n) < m < n + p(m)
$$
(Here $p(m)$ is the least prime factor of $m$.)
-/
@[problem_status open]
theorem erdos_463 : ∃ (f : ℕ → ℕ) (_ : Tendsto f atTop atTop),
    ∀ᶠ n in atTop,
      ∃ m, ¬m.Prime ∧
        n + f n < m ∧ m < n + m.minFac :=
  sorry
