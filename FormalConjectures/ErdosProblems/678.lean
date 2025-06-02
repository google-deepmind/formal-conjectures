/-
Copyright 2025 The Formal Conjectures Authors.

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

/-!
# Erdős Problem 678
*Reference:* [erdosproblems.com/678](https://www.erdosproblems.com/678)
-/

open Asymptotics Filter Finset

/--
Write $M(n, k)$ be the least common multiple of ${n+1, \dotsc, n+k}$, denoted here as
`lcmInterval n k`.
-/
def lcmInterval (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

/--
The referee of [Er79] found the example $M(96, 7) > M(104, 8)$, showing that there are cases where
$M(n, k) > M(m, k + 1)$ with $m \geq n + k$.
[Er79] Erdős, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.
-/
@[category test]
lemma lcmInterval_lt_example1 : lcmInterval 104 8 < lcmInterval 96 7 := by decide

/--
The referee of [Er79] found the example $M(132, 7) > M(139, 8)$, showing that there are cases where
$M(n, k) > M(m, k + 1)$ with $m \geq n + k$.
[Er79] Erdős, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.
-/
@[category test]
lemma lcmInterval_lt_example2 : lcmInterval 139 8 < lcmInterval 132 7 := by decide

/--
Cambie [Ca24] found the example $M(52, 7) > M(62, 8)$.
[Ca24] S. Cambie, Resolution of an Erdős' problem on least common multiples. arXiv:2410.09138 (2024).
-/
@[category test]
lemma lcmInterval_lt_example3 : lcmInterval 62 8 < lcmInterval 52 7 := by decide

/--
Cambie [Ca24] found the example $M(36, 8) > M(48, 9)$.
[Ca24] S. Cambie, Resolution of an Erdős' problem on least common multiples. arXiv:2410.09138 (2024).
-/
@[category test]
lemma lcmInterval_lt_example4 : lcmInterval 47 9 < lcmInterval 36 8 := by decide

/--
Write $M(n, k)$ be the least common multiple of ${n+1, \dotsc, n+k}$.
Let $k \geq 3$. Are there infinitely many $m, n$ with $m \geq n + k$ such that
$$
M(n, k) > M(m, k + 1)
$$?
The answer is yes, as proved in a strong form by Cambie [Ca24].
[Ca24] S. Cambie, Resolution of an Erdős' problem on least common multiples. arXiv:2410.09138 (2024).
-/
@[category research solved, AMS 11]
theorem erdos_678 :
    (∀ k, 3 ≤ k → {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Infinite) ↔
      answer(True) := by
  sorry
