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

import FormalConjectures.Util.Attributes.Basic
import FormalConjecturesForMathlib.Data.Nat.MaxPrimeFac

/-!
# Erdős Problem 372

*Reference:* [erdosproblems.com/372](https://www.erdosproblems.com/372)

Conjectured by Erdős and Pomerance. Proved by Balog, who showed the stronger quantitative result
that this holds for $\gg \sqrt{x}$ many $n\leq x$, for all large $x$.
-/

namespace Erdos372

/--
Let $P(n)$ denote the largest prime factor of $n$. There are infinitely many $n$ such that
$P(n)>P(n+1)>P(n+2)$.
-/
@[category research solved, AMS 11]
theorem erdos_372 :
    {n : ℕ | Nat.maxPrimeFac n > Nat.maxPrimeFac (n + 1) ∧
      Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac (n + 2)}.Infinite := by
  sorry

end Erdos372
