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
# Betrothed numbers

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Betrothed_numbers)
- [OEIS A005276](https://oeis.org/A005276)
-/

namespace BetrothedNumbers

open scoped ArithmeticFunction.sigma

/--
Two natural numbers $m$ and $n$ are **betrothed**  (or quasi-amicable) if $\sigma(m) = \sigma(n) = m + n + 1$,
where $\sigma$ is the sum-of-divisors function. Equivalently, the sum of the proper divisors
of $m$ equals $n + 1$, and the sum of the proper divisors of $n$ equals $m + 1$.
-/
@[mk_iff]
structure IsBetrothed (m n : ℕ) : Prop where
  left : σ 1 m = m + n + 1
  right : σ 1 n = m + n + 1

/-- The smallest known betrothed pair $(48, 75)$. -/
@[category test, AMS 11]
theorem betrothed_48_75 : IsBetrothed 48 75 := by
  constructor <;> decide

/-- `IsBetrothed` is symmetric. -/
@[category test, AMS 11]
theorem IsBetrothed.symm {m n : ℕ} (h : IsBetrothed m n) : IsBetrothed n m := by
  rw [isBetrothed_iff] at *
  omega

/--
**Same parity betrothed numbers conjecture.**
Do there exist betrothed numbers $(m, n)$ where both have the same parity
(both even or both odd)?

All known betrothed pairs consist of one even and one odd number.

-/
@[category research open, AMS 11]
theorem same_parity_betrothed :
    answer(sorry) ↔ ∃ m n : ℕ, IsBetrothed m n ∧ (Even m ↔ Even n) := by
  sorry

/--
**Infinitude of betrothed numbers conjecture.**
Are there infinitely many betrothed number pairs?

-/
@[category research open, AMS 11]
theorem infinitely_many_betrothed :
    answer(sorry) ↔ {p : ℕ × ℕ | p.1 < p.2 ∧ IsBetrothed p.1 p.2}.Infinite := by
  sorry

end BetrothedNumbers
