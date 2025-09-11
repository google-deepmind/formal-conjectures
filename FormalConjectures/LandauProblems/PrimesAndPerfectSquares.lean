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
Are there infinitely many primes $p$ such that $p − 1$ is a perfect square? In other words: Are there infinitely many primes of the form $n^2 + 1$?
-/
@[problem_status open]
theorem infinite_prime_sq_add_one : {n : ℕ | Prime (n^2 + 1)}.Infinite := by
  sorry
