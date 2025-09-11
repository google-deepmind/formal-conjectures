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

import FormalConjectures.Util.ProblemImports

/--
Can every even integer greater than 2 be written as the sum of two primes?
-/
@[problem_status open]
theorem goldbach (n : ℕ) (hn : 2 < n) (hn_even : Even n) :
    ∃ p q, Prime p ∧ Prime q ∧ n = p + q := by
  sorry
