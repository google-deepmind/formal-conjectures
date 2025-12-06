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

-- import FormalConjectures.Util.ProblemImports
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1106

*Reference:* [erdosproblems.com/1064](https://www.erdosproblems.com/1106)
-/

open Nat Finset Filter Topology

namespace Erdos1106

/-- The partition function p(n) is the number of ways to write n as a sum of positive
integers (where the order of the summands does not matter). -/
def p : ℕ → ℕ
| 0 => 1
| n + 1 => (p n) + ∑ k ∈  range (n + 1),
    if n + 1 - (k + 1) < (k + 1) then 0
    else p (n + 1 - (k + 1) - (k + 1))

/-- let $F(n)$ be distinct prime factor of $∏_{i= 1} ^ {n} p(n)$ -/
def F : ℕ → ℕ := fun n => (∏ i ∈ Icc 1 n, p i).primeFactors.card

/--
Let $p(n)$ be the partition number of $n$ and $F(n)$ be distinct prime factor of
$∏_{i= 1} ^ {n} p(n)$, then $F(n)$ tendsto infinity when $n$ tendsto infinity, and
is $F(n)>n$ for sufficient large $n$.
-/
@[category research open, AMS 11]
theorem erdos_1106 : Tendsto F atTop atTop ∧ ∃ N, ∀ n > N, F n > n := sorry


end Erdos1106
