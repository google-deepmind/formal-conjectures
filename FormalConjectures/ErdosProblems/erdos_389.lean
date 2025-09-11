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

-- Erdos Problems URL: https://www.erdosproblems.com/389
import FormalConjectures.Util.ProblemImports

/--
Is it true that for every $n geq 1$ there is a $k$ such that
$$
  n(n + 1) \cdots (n + k - 1) \mid (n + k) \cdots (n + 2k - 1)?
$$
-/
@[problem_status open]
theorem erdos_389 (n : ℕ) (h : 1 ≤ n) :
    ∃ k ≥ 1,
      ∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k, (n + k + i) :=
  sorry

/--
Bhavik Mehta has computed the minimal such $k$ for $1 \leq n \leq 18$.
For example, the minimal $k$ for $n = 4$ is $207$.
-/
@[problem_status solved]
theorem erdos_389.variants.mehta_four :
    IsLeast
      { k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (4 + i) ∣ ∏ i ∈ Finset.range k, (4 + k + i) }
      207 :=
  sorry
