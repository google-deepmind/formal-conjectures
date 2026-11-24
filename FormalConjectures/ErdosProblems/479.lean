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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 479

*Reference:* [erdosproblems.com/479](https://www.erdosproblems.com/479)
-/

@[expose] public section

namespace Erdos479

/--
Is it true that, for every integer $k\neq 1$, there are infinitely many $n$ such that
$2^n\equiv k\pmod{n}$?
-/
@[category research open, question, AMS 11]
theorem erdos_479 : ∀ᵉ (k : ℤ) (k ≠ 1),
    { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Infinite := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
For every $i \geq 1$ there are infinitely many $n$ such that $2^n \equiv -2^i \pmod{n}$, that is,
$n \mid 2^n + 2^i$. This answers the question for $k = -2, -4, -8, -16, \ldots$. On the
erdosproblems.com forum (December 2025), Tang recorded the question as open for every fixed $k$
other than $k \in \{0, -1, -2\}$ and $k = 2^i$.

Starting from $n = 2^i$, replace $n$ by $np$, where $p$ is a prime for which $2$ has order
$2(n - i)$ modulo $p$. Such a prime exists by Bang's theorem, and $np \mid 2^{np} + 2^i$ follows
from Fermat's little theorem modulo $p$ and from $2(n - i) \mid p - 1$ modulo $n$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/1b13018b741a8b89ec0e6ec797f1c935d6b97fd2/ErdosLean/Erdos479.lean#L336-L367"]
theorem erdos_479.variants.neg_two_pow :
    ∀ i ≥ 1, { n : ℕ | (2 : ℤ) ^ n ≡ -(2 ^ i) [ZMOD (n : ℤ)] }.Infinite := by
  sorry

end Erdos479
