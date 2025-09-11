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

-- Erdos Problems URL: https://www.erdosproblems.com/303
import FormalConjectures.Util.ProblemImports

/--Is it true that in any finite colouring of the integers there exists a monochromatic solution to `1/a=1/b+1/c` with distinct `a,b,c`?-/
@[problem_status solved]
theorem erdos_303 :
    --For any finite colouring of the integers
    ∀ (𝓒 : ℤ → ℤ), (Set.range 𝓒).Finite →
      --There exists integers `a, b, c`
      ∃ (a b c : ℤ),
      --that are non-zero and distinct.
      [a, b, c, 0].Nodup ∧
      --`a, b, c` satisfy the equation
      (1/a : ℝ) = 1/b + 1/c ∧
      --`a, b, c` have the same color
      (𝓒 '' {a, b, c}).Subsingleton := by
  sorry
