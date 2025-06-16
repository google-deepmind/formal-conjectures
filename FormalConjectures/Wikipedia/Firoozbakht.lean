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

import FormalConjectures.Util.ProblemImports

/-!
# Firoozbakht's conjecture

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Firoozbakht%27s_conjecture)
- [primepuzzles](https://www.primepuzzles.net/conjectures/conj_030.htm)
-/

open Real

/--
The sequence of $\sqrt[n]{p_n}$ where $p_n$ is the n:th prime number.
-/
noncomputable def firoozbakhtSeq (n : ℕ) : ℝ :=
  (n.nth Prime)^(1/(n + 1) : ℝ)

/--
**Firoozbakht's conjecture**
The inequality $\sqrt[n+1]{p_{n+1}} < \sqrt[n]{p_n}$ holds for all prime numbers $p_n$.
-/
@[category research open, AMS 11]
theorem firoozbakht_conjecture (n : ℕ) :
    firoozbakhtSeq (n+1) < firoozbakhtSeq n := by
  sorry

/--
The inequality $p_{n+1}-p_n < (\log p_n)^2-\log p_n$ holds for all $n>4$.
A consequence of Firuzbakht's conjecture.
-/
@[category research solved, AMS 11]
theorem firoozbakht_conjecture_consequence (n : ℕ) (hn : 3 < n) (P : type_of% firoozbakht_conjecture) :
    (n+1).nth Prime - n.nth Prime < (log (n.nth Prime))^2 - log (n.nth Prime) := by
  sorry
