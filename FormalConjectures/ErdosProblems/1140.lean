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
# Erdős Problem 1140

Are there infinitely many $n$ such that $n - 2x^2$ is prime for all $x$ with $2x^2 < n$?

*Reference:* [erdosproblems.com/1140](https://www.erdosproblems.com/1140)

[Va99] Vaughan, R. C., *The Hardy-Littlewood Method*, 2nd ed., 1997.

[EpGi10] Epure, R. and Gica, A., _Principal quadratic real fields in connection with some
additive problems_. Bull. Math. Soc. Sci. Math. Roumanie (N.S.) (2010), 251–259.

[MoWi89] Mollin, R. A. and Williams, H. C., _Period four and real quadratic fields of class
number one_. Proc. Japan Acad. Ser. A Math. Sci. (1989), 89–93.
-/

namespace Erdos1140

/-- The property that $n - 2x^2$ is prime for all $x$ with $2x^2 < n$. -/
def AllShiftsArePrime (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

/--
Erdős Problem #1140 [Va99, 1.5] (Disproved):

Do there exist infinitely many $n$ such that $n - 2x^2$ is prime for all $x$
with $2x^2 < n$?

The known such $n$ are $2, 5, 7, 13, 31, 61, 181, 199$. Epure and Gica [EpGi10]
proved that the only such $n \equiv 1 \pmod{4}$ are $5, 13, 61, 181$, and the only
such $n \equiv 3 \pmod{4}$ are $7, 31, 199$ (with at most one exception,
using [MoWi89]).
This implies that, with at most one exception, the list above is complete.
-/
@[category research solved, AMS 11]
theorem erdos_1140 :
    answer(False) ↔ Set.Infinite {n : ℕ | AllShiftsArePrime n} := by
  sorry

end Erdos1140
