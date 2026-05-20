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

open Finset

/--
A243106: The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.
-/
def a (n : ℕ) : Int :=
  (Icc 1 n).sum fun k : ℕ =>
    (if Nat.Prime k then (-1 : Int) else 1) * (10 : Int) ^ k


theorem a_one : a 1 = 10 := by
  sorry

theorem a_two : a 2 = -90 := by
  sorry

theorem a_three : a 3 = -1090 := by
  sorry

theorem a_four : a 4 = 8910 := by
  sorry


/--
Conjecture: For any natural number $n$ and base $b > 4$, the absolute value of any sum of the form
$\sum_{k=1}^n \sigma_k b^k$ where $\sigma_k \in \{-1, 1\}$ only contains digits
belonging to $\{0, 1, b-2, b-1\}$ when expressed in base $b$.
This is the formalization of the conjecture for general base $b$.
-/
theorem oeis_243106_conjecture_0 (b n : ℕ) (hb : b ≥ 5) :
  ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
    let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
    ∀ d ∈ (b.digits x.natAbs),
      d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 :=
by sorry
