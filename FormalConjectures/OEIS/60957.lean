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

import FormalConjecturesUtil

/-!
# Number of different products of subsets of $\{1, 2, \dots, n\}$

The number of distinct products (including the empty product 1) of any subset
of $\{1, 2, \dots, n\}$.

*References:*
- [A060957](https://oeis.org/A060957)-/

namespace OeisA60957

/-- Number of different products of any subset of $\{1, 2, \dots, n\}$. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.image (·.prod id)).card

@[category test, AMS 5 11]
theorem a_0 : a 0 = 1 := by
  decide

@[category test, AMS 5 11]
theorem a_1 : a 1 = 1 := by
  decide

@[category test, AMS 5 11]
theorem a_2 : a 2 = 2 := by
  decide

@[category test, AMS 5 11]
theorem a_3 : a 3 = 4 := by
  decide

@[category test, AMS 5 11]
theorem a_4 : a 4 = 8 := by
  decide

@[category test, AMS 5 11]
theorem a_5 : a 5 = 16 := by
  decide

/-- The set of products of subsets of $\{1, \dots, n\}$. -/
def productsOfSubsets (n : ℕ) : Set ℕ :=
  {m : ℕ | ∃ s ⊆ Finset.Icc 1 n, m = s.prod id}

/--
Conjecture: let $p \le n$ be prime. If $m$ and $p^a m$ are two such products, then so is $p^k m$
for all $0 < k < a$.
- Yan Sheng Ang, Feb 13 2020
-/
@[category research open, AMS 5 11]
theorem conjecture (n : ℕ) (p : ℕ) (hp : p.Prime) (hpn : p ≤ n)
    (m a_exp : ℕ) (h1 : m ∈ productsOfSubsets n) (h2 : p ^ a_exp * m ∈ productsOfSubsets n)
    (k : ℕ) (hk1 : 0 < k) (hk2 : k < a_exp) :
    p ^ k * m ∈ productsOfSubsets n := by
  sorry

end OeisA60957
