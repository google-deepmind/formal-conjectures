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
# Brocard's Conjecture

For every n ≥ 2, between the squares of the n-th and (n+1)-th primes,
there are at least four prime numbers.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Brocard%27s_conjecture)
-/

@[category research open, AMS 11]
theorem brocard_conjecture :
  ∀ n : ℕ, n ≥ 2 →
    let prev := Nat.nth Prime n;
    let next := Nat.nth Prime (n+1);
    let primesInBetween := (Finset.Ioo (prev^2) (next^2)).filter Nat.Prime
    primesInBetween.card ≥ 4 := by
  sorry
