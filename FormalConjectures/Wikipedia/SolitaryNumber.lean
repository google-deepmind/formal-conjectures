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
# Solitary Numbers


*References:*
- [Solitary number (Wikipedia)](https://en.wikipedia.org/wiki/Solitary_number)
- [Solitary number large clubs (Wikipedia)](https://en.wikipedia.org/wiki/Solitary_number#Large_clubs)
-/

open ArithmeticFunction.sigma

namespace SolitaryNumber

/--
Two positive integers $m$ and $n$ are friendly if they have the same abundancy index, that
is $\sigma(m) / m = \sigma(n) / n$, expressed via cross-multiplication to avoid rationals.
-/
def Friendly (m n : ℕ) : Prop := 0 < m ∧ 0 < n ∧ σ 1 m * n = σ 1 n * m

/--
A positive integer $n$ is solitary if every friend of $n$ is equal to $n$, i.e. its
abundancy class is the singleton $\{n\}$.
-/
def IsSolitary (n : ℕ) : Prop := 0 < n ∧ ∀ m, Friendly m n → m = n

/--
**Is 10 a solitary number?**  The smallest positive integer whose solitary status is
currently unresolved is $10$, with abundancy index $\sigma(10) / 10 = 9/5$.
-/
@[category research open, AMS 11]
theorem is_ten_solitary : answer(sorry) ↔ IsSolitary 10 := by
  sorry

/--
**Existence of an infinite club.**  A *club* is an abundancy equivalence class, i.e.
the set of all positive integers friendly with a given $n$.  It is unknown whether any club
is infinite.
-/
@[category research open, AMS 11]
theorem infinite_club_exists :
    answer(sorry) ↔ ∃ n, 0 < n ∧ {m : ℕ | Friendly m n}.Infinite := by
  sorry

end SolitaryNumber
