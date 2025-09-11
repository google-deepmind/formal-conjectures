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

-- Erdős Problems URL: https://www.erdosproblems.com/412
import FormalConjectures.Util.ProblemImports

/--Let `σ_1(n)=σ(n)`, the sum of divisors function, and `σ_k(n)=σ(σ_{k−1}(n))`-/
abbrev σ (k : ℕ) : ℕ → ℕ := (ArithmeticFunction.sigma 1)^[k]

lemma sigma_0 : σ 0 = id := rfl

lemma sigma_1 : σ 1 = ArithmeticFunction.sigma 1 := rfl

/--Is it true that, for every `m,n≥2`, there exist some `i,j` such that `σ_i(m)=σ_j(n)`?-/
@[problem_status open]
theorem erdos_412 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ i j, σ i m = σ j n := by
  sorry
