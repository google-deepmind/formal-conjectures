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

-- Erdos Problems URL: https://www.erdosproblems.com/727
import FormalConjectures.Util.ProblemImports

open scoped Nat

/--
Let k≥2. Does ((n+k)!)^2∣(2n)! for infinitely many n?
-/
@[problem_status open]
theorem erdos_727
    (k : ℕ)
    (hk : k > 1) :
    Set.Infinite {n : ℕ | (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)} :=
  sorry

/--
It is open even for k=2.
Let k=2. Does ((n+k)!)^2∣(2n)! for infinitely many n?
-/
@[problem_status open]
theorem erdos_727_variants.k_2
    (k : ℕ)
    (hk : k = 2) :
    Set.Infinite {n : ℕ | (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)} :=
  sorry

/--
Balakran proved this holds for  k=1.

Let k=1. Does ((n+k)!)^2∣(2n)! for infinitely many n?

Status: Solved
-/
@[problem_status solved]
theorem erdos_727_variants.k_1
    (k : ℕ)
    (hk : k = 1) :
    Set.Infinite {n : ℕ | (n + k)! ^ 2 ∣ (2 * n)!} :=
  sorry

/--
Erdős, Graham, Ruzsa, and Straus observe that the method of Balakran can be further used to prove that there are infinitely many n
 such that
(n+k)!(n+1)!∣(2n)!

Status: Solved
-/
@[problem_status solved]
theorem erdos_727_variants.k_1_2
    (k : ℕ)
    (hk : k > 1) :
    Set.Infinite {n : ℕ | (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)} :=
  sorry
