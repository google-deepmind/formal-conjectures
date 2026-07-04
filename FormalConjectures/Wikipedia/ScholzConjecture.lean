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
# Scholz conjecture on addition chains

An *addition chain* for a positive integer `n` is a strictly increasing sequence
`1 = a₀ < a₁ < ⋯ < a_r = n` in which every entry after the first is the sum of two
(not necessarily distinct) earlier entries. The *length* `ℓ(n)` is the minimal number
of addition steps `r` over all such chains.

The **Scholz conjecture** (also known as the Scholz–Brauer or Brauer–Scholz conjecture)
asserts that for every positive integer `n`,
$$\ell(2^n - 1) \le n - 1 + \ell(n).$$

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Scholz_conjecture)
- [MathWorld](https://mathworld.wolfram.com/ScholzConjecture.html)
-/

namespace ScholzConjecture

/-- `IsAdditionChain c` asserts that the list `c` is an addition chain: it starts at
`1`, is strictly increasing, and every entry after the first is the sum of two (not
necessarily distinct) earlier entries. The step condition is phrased with the safe
`getElem?` accessor: for each valid index `i ≠ 0` there are earlier indices `j, k` with
`c[i]? = c[j]? + c[k]?` (as `Option`-valued sums). -/
def IsAdditionChain (c : List ℕ) : Prop :=
  c.head? = some 1 ∧
  c.Pairwise (· < ·) ∧
  ∀ x ∈ c, x ≠ 1 → ∃ y ∈ c, ∃ z ∈ c, x = y + z

/-- The length `ℓ(n)` of `n`: the minimal number of addition steps (number of entries
minus one) over all addition chains ending at `n`. -/
noncomputable def additionChainLength (n : ℕ) : ℕ :=
  sInf { r | ∃ c : List ℕ, IsAdditionChain c ∧ c.getLast? = some n ∧ c.length = r + 1 }

local notation "ℓ(" n ")" => additionChainLength n

/--
The Scholz conjecture, also known as the Scholz-Brauer conjecture, asserts that
for every positive integer $n$, the addition-chain length of $2^n - 1$ is at most
$n - 1 + \ell(n)$.

References: Wikipedia and MathWorld.
-/
@[category research open, AMS 11 68]
theorem scholz_conjecture (n : ℕ) (hn : 0 < n) :
    ℓ(2 ^ n - 1) ≤ n - 1 + ℓ(n) := by
  sorry

end ScholzConjecture
