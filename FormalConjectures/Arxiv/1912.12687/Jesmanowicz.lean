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
module

public import FormalConjecturesUtil

/-!
# Jeśmanowicz' conjecture

*Reference:* [arXiv:1912.12687](https://arxiv.org/abs/1912.12687)

Let `(a, b, c)` be pairwise coprime positive integers with `a ^ 2 + b ^ 2 = c ^ 2`.
Jeśmanowicz conjectured that the only positive integer solution of `a ^ x + b ^ y = c ^ z`
is `(x, y, z) = (2, 2, 2)`.
-/

@[expose] public section

namespace Arxiv.«1912.12687»

/--
**Jeśmanowicz' conjecture**: if `a`, `b`, and `c` are pairwise coprime positive integers
with `a ^ 2 + b ^ 2 = c ^ 2`, then the only positive integer solution of
`a ^ x + b ^ y = c ^ z` is `x = y = z = 2`.
-/
@[category research open, AMS 11]
theorem jesmanowicz_conjecture
    (a b c x y z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcop : ({a, b, c} : Set ℕ).Pairwise Nat.Coprime)
    (hpyth : a ^ 2 + b ^ 2 = c ^ 2)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : a ^ x + b ^ y = c ^ z) :
    x = 2 ∧ y = 2 ∧ z = 2 := by
  sorry

end Arxiv.«1912.12687»
