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

-- Erdos Problems URL: https://www.erdosproblems.com/873
import FormalConjectures.Util.ProblemImports

/--Let `a` be some sequence of natural numbers. We set `F(A,X,k)` to be the number of `i` such that
`[a_i,a_{i+1}, … ,a_{i+k−1}] < X`, where the left-hand side is the least common multiple.-/
noncomputable abbrev F (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (Finset.range k).gcd (fun m => a (i + m)) < X}.encard

/--Let `A={a_1 < a_2 <⋯} ⊆ ℕ` and let `F(A,X,k)` count the number of `i` such that
`[a_i,a_{i+1}, … ,a_{i+k−1}] < X`, where the left-hand side is the least common multiple.
Is it true that, for every `ϵ > 0`, there exists some `k` such that `F(A,X,k) < X^ϵ`?-/
@[problem_status open]
theorem erdos_873 (a : ℕ → ℕ) (ha : StrictMono a) (ε : ℝ) (hε : 0 < ε):
    ∃ k, ∀ X > 0, F a X k < (X^ε).toEReal :=
  sorry
