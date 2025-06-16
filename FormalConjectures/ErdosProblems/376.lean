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
# Erdős Problem 376

*Reference:* [erdosproblems.com/376](https://www.erdosproblems.com/376)
-/
/--
Are there infinitely many $n$ such that ${2n\choose n}$ is coprime to $105$?
-/
@[category research open, AMS 11]
theorem erdos_376 : { n | ((2 * n).choose n).Coprime 105 }.Infinite ↔ answer(sorry) := by
  sorry

/--
Erdős, Graham, Ruzsa, and Straus [EGRS75] have shown that, for any two odd primes $p$ and $q$,
there are infinite many $n$ such that ${2n\choose n}$ is coprime to $pq$.
-/
@[category research solved, AMS 11]
theorem erdos_376.variants.prime {p q : ℕ} (h₁ : p.Prime)
    (h₂ : Odd p) (h₃ : q.Prime) (h₄ : Odd q) :
    { n | ((2 * n).choose n).Coprime (p * q) }.Infinite := by
  sorry
