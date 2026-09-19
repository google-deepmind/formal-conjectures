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
# Pairs $\{j, k\}$ with $0 < j < k \le n$, $k \equiv 1 \pmod j$, and $\pi(jn) \mid \pi(kn)$

Let $\pi$ denote the prime counting function. The sequence $a(n)$ counts the number of pairs
$(j, k)$ with $0 < j < k \le n$ and $k \equiv 1 \pmod j$ such that $\pi(jn)$ divides $\pi(kn)$.

*References:*
- [A238224](https://oeis.org/A238224)
-/

namespace OeisA238224

/-- $a(n)$ is the number of pairs $(j, k)$ with $0 < j < k \le n$ and $k \equiv 1 \pmod j$
such that $\pi(j \cdot n)$ divides $\pi(k \cdot n)$. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico 1 n,
    ∑ q ∈ Finset.Icc 1 ((n - 1) / j),
      let k := j * q + 1
      if Nat.primeCounting (j * n) ∣ Nat.primeCounting (k * n) then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/--
Conjecture: $a(n) > 0$ for all $n > 1$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : 0 < a n := by
  sorry

end OeisA238224
