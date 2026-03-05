/-
Copyright 2026 The Formal Conjectures Authors.

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
# Erdős Problem 460

*Reference:* [erdosproblems.com/460](https://www.erdosproblems.com/460)

This problem arose in work of Eggleton, Erdős, and Selfridge.

[Er77c] Erdős, P., *Problems and results on combinatorial number theory III*,
Number Theory Day (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72.
-/

open Finset Filter Classical

namespace Erdos460

/-- The greedy coprime-complement sequence for a given $n$.
$a_0 = 0$ and $a_{k+1}$ is the least integer greater than $a_k$ such that
$\gcd(n - a_{k+1}, n - a_i) = 1$ for all $i \leq k$. -/
noncomputable def erdos460Seq (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sInf {m : ℕ | erdos460Seq n k < m ∧
      ∀ i : ℕ, i ≤ k → Nat.Coprime (n - m) (n - erdos460Seq n i)}

/-- The sum $\sum_{0 < a_i < n} 1/a_i$ for the greedy coprime-complement
sequence. -/
noncomputable def erdos460Sum (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun k =>
    0 < erdos460Seq n k ∧ erdos460Seq n k < n)).sum
    (fun k => (1 : ℝ) / (erdos460Seq n k : ℝ))

/--
Erdős Problem 460 [Er77c]:

Does $\sum_{0 < a_i < n} 1/a_i \to \infty$ as $n \to \infty$, where
$(a_k)$ is the greedy sequence with $a_0 = 0$ and each $a_{k+1}$ the least
integer greater than $a_k$ making $\gcd(n - a_{k+1}, n - a_i) = 1$ for all
$i \leq k$?
-/
@[category research open, AMS 11]
theorem erdos_460 :
    answer(sorry) ↔ Tendsto erdos460Sum atTop atTop := by
  sorry

end Erdos460
