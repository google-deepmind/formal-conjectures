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

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Scholz_conjecture)
- [MathWorld](https://mathworld.wolfram.com/ScholzConjecture.html)
- [Tall22](https://arxiv.org/abs/2210.13812) Amadou Tall. "The Scholz conjecture on addition
  chain is true for infinitely many integers with $\ell(2n) = \ell(n)$." _arXiv:2210.13812_ (2022).
  Also available as [ePrint 2023/020](https://eprint.iacr.org/2023/020).
-/

namespace ScholzConjecture

/-- An *addition chain* is a strictly increasing sequence
$1 = a_0 < a_1 < \cdots < a_r$ in which every entry after the first is the sum of two
(not necessarily distinct) earlier entries.

`IsAdditionChain c` asserts that the list $c$ is such a chain: it starts at $1$, is
strictly increasing, and every entry other than $1$ is a sum of two entries of $c$. -/
def IsAdditionChain (c : List ℕ) : Prop :=
  c.head? = some 1 ∧
  c.Pairwise (· < ·) ∧
  ∀ x ∈ c, x ≠ 1 → ∃ y ∈ c, ∃ z ∈ c, x = y + z

/-- The *length* $\ell(n)$ of $n$: the minimal number of addition steps (the number of
entries minus one) over all addition chains ending at $n$. -/
noncomputable def additionChainLength (n : ℕ) : ℕ :=
  sInf { r | ∃ c : List ℕ, IsAdditionChain c ∧ c.getLast? = some n ∧ c.length = r + 1 }

local notation "ℓ(" n ")" => additionChainLength n

/--
The Scholz conjecture, also known as the Scholz-Brauer conjecture, asserts that
for every positive integer $n$, the addition-chain length of $2^n - 1$ is at most
$n - 1 + \ell(n)$.
-/
@[category research open, AMS 11 68]
theorem scholz_conjecture (n : ℕ) (hn : 0 < n) :
    ℓ(2 ^ n - 1) ≤ n - 1 + ℓ(n) := by
  sorry

end ScholzConjecture
