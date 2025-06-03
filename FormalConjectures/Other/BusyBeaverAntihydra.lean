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
# Busy Beaver Challenge: Antihydra

*Reference:* [bbchallenge](https://wiki.bbchallenge.org/wiki/Antihydra)
-/

/--
Antihydra is a sequence starting at 8, and iterating the function
$$H(n) = \left\lfloor \frac {3n}2 \right\rfloor.$$
The conjecture states that the cumulative number of odd values in this sequence
is never more than twice the cumulative number of even values

It is a relatively new open problem with, so it might be solvable, although
seems quite hard. It is equivalent to non-termination of a particular 6-state
turing machine.
-/
@[category research open, AMS 5, AMS 11]
theorem busy_beaver_antihydra (a : ℕ → ℕ) (b : ℕ → ℤ)
    (a_ini : a 0 = 8) (a_rec : ∀ n, a (n+1) = (3*a n/2 : ℕ)) (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n+1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, b n ≥ 0 := by
  sorry

/--
Alternative statement of busy_beaver_antihydra
using set size comparison instead of a recurrent sequence b.
-/
@[category research open, AMS 5, AMS 11]
theorem busy_beaver_antihydra.variants.set (a : ℕ → ℕ)
    (a_ini : a 0 = 8) (a_rec : ∀ n, a (n+1) = (3*a n/2 : ℕ)) :
    ∀ n, ((Finset.Ico 0 n).filter fun x ↦ Odd (a x)).card ≤
        2*((Finset.Ico 0 n).filter fun x ↦ Even (a x)).card := by
  sorry
