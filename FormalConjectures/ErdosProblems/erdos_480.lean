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

-- Erdos Problems URL: https://www.erdosproblems.com/go_to/480
import FormalConjectures.Util.ProblemImports


/--
Let `x_1,x_2,…∈[0,1]` be an infinite sequence. Is it true that there are infinitely many `m,n`
such that `|x_{m+n}−x_n|≤1/(√5 n)`?
-/
theorem erdos_480
    (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Icc 0 1) :
    {(m, n) | |x (m + n) - x n| ≤ 1 / (√5 * n)}.Infinite := by
  sorry


/--
For any `ϵ>0` there must exist some `n` such that there are infinitely many `m`
for which `|x_{m+n}−x_m|<1/((c−ϵ)n)`, where
`c=1+∑_{k≥1} 1/(F_{2k} =2.535⋯`
and `F_m` is the `m`th Fibonacci number. This constant is best possible.
-/
theorem erdos_480.variants.chung_graham :
    let c : ℝ := 1 + ∑' (k : ℕ+), (1 : ℝ) / (2*k : ℕ).fib
    IsGreatest {C : ℝ | C > 0 ∧ ∀ (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Icc 0 1),
      ∀ ε ∈ Set.Ioo 0 C, ∃ n, {m | |x (n + m) - x m| < 1 / ((C - ε) * n)}.Infinite}
    c := by
  sorry
