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

-- Erdos Problems URL: https://www.erdosproblems.com/383
import FormalConjectures.Util.ProblemImports

/--
Is it true that for every $k$ there are infinitely many primes $p$ such that the largest prime
divisor of
$$
  \prod_{i = 0}^k (p ^ 2 + i)
$$
is $p$?
-/
@[problem_status open]
theorem erdos_383 (k : ℕ) :
    {p : ℕ | p.Prime ∧ Nat.maxPrimeFac (∏ i in Finset.Icc 0 k, (p ^ 2 + i)) = p}.Infinite := by
  sorry
