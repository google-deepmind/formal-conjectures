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
# The Erdős–Moser equation

For positive integers $k$ and $m$, let

$$S_k(m)=1^k+2^k+\cdots+(m-1)^k.$$

The Erdős–Moser conjecture says that $S_k(m)=m^k$ has only the solution
$(k,m)=(1,3)$.

*References:*
* [Wikipedia: Erdős–Moser equation](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Moser_equation)
* B. C. Kellner,
  [On stronger conjectures that imply the Erdős–Moser conjecture](https://arxiv.org/abs/1003.1646)
-/

namespace ErdosMoser

/-- The power sum $S_k(m)=\sum_{i=1}^{m-1} i^k$. -/
def powerSum (k m : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico 1 m, i ^ k

/-- The only positive solution of $S_k(m)=m^k$ is $(k,m)=(1,3)$. -/
@[category research open, AMS 11]
theorem erdos_moser_conjecture :
    ∀ k m : ℕ, 0 < k → 0 < m → powerSum k m = m ^ k → k = 1 ∧ m = 3 := by
  sorry

/-- The pair $(1,3)$ is the trivial solution of the Erdős–Moser equation. -/
@[category test, AMS 11]
theorem powerSum_one_three : powerSum 1 3 = 3 ^ 1 := by
  decide

/-- For $k=2$ and $m=3$, the left side is $1^2+2^2=5$, not $3^2$. -/
@[category test, AMS 11]
theorem powerSum_two_three : powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2 := by
  decide

/-- Zero is a solution for every positive exponent, so the conjecture must require $m>0$. -/
@[category test, AMS 11]
theorem powerSum_zero (k : ℕ) (hk : 0 < k) : powerSum k 0 = 0 ^ k := by
  simp [powerSum, Nat.zero_pow hk]

end ErdosMoser
