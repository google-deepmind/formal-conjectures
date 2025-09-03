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
# Feit-Thompson conjecture on primes

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_conjecture)
-/

/--
There are no distinct primes $p$ and $q$ such that $\frac{q^p - 1}{q - 1}$ divides $\frac{p^q - 1}{p - 1}$
-/
@[category research open, AMS 11]
theorem feit_thompson_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p < q) :
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1) := by
  sorry
