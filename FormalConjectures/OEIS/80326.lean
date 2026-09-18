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
# Denominator of $\sum_{k=1}^n k^{\mu(k)}$

The sequence $a(n)$ is the denominator of $\sum_{k=1}^n k^{\mu(k)}$, where $\mu$ is the
Möbius function.

*References:*
- [A080326](https://oeis.org/A080326)-/

namespace OeisA80326

open ArithmeticFunction

/-- $k^{\mu(k)}$ as a rational number. -/
def term (k : ℕ) : ℚ :=
  let mu := (moebius k : ℤ)
  if mu = 1 then k
  else if mu = 0 then 1
  else (1 : ℚ) / k

/-- Denominator of $\sum_{k=1}^n k^{\mu(k)}$. -/
def a (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.Icc 1 n, term k).den

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 6 := by
  decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by
  decide +native

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 30 := by
  decide +native

/--
Conjecture: $a(n) = \text{primorial}(n)$ for infinitely many $n$.-/
@[category research open, AMS 11]
theorem conjecture : {n : ℕ | a n = primorial n}.Infinite := by
  sorry

end OeisA80326
