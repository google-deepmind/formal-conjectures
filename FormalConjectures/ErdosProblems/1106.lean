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
# Erdős Problem 1106

*Reference:* [erdosproblems.com/1064](https://www.erdosproblems.com/1106)
-/

open Nat Finset Filter Topology

namespace Erdos1106

/-- The partition function p(n) is the number of ways to write n as a sum of positive
integers (where the order of the summands does not matter). -/
def p : ℕ → ℕ := fun n => Fintype.card (Nat.Partition n)

/--
Let $p(n)$ be the partition number of $n$ and $F(n)$ be the number of distinct prime factors of
$∏_{i= 1} ^ {n} p(n)$, then $F(n)$ tends to infinity when $n$ tends to infinity.
-/
@[category research open, AMS 11]
theorem erdos_1106 : Tendsto (fun n => #(∏ i ∈ Icc 1 n, p i).primeFactors) atTop atTop := sorry

/-- Let $p(n)$ be the partition number of $n$ and $F(n)$ be the number of distinct prime factors of
$∏_{i= 1} ^ {n} p(n)$, $F(n)>n$ for sufficiently large $n$.-/
@[category research open, AMS 11]
theorem erdos_1106_k2 :  ∀ᶠ n in atTop, #(∏ i ∈ Icc 1 n, p i).primeFactors > n := sorry

end Erdos1106
