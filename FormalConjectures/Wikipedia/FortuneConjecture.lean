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
import Mathlib.NumberTheory.Primorial

/-!
# Fortune's Conjecture

A *Fortunate number* is the smallest integer $m > 1$ such that $p_n\# + m$ is prime,
where $p_n\#$ denotes the $n$-th *primorial* (the product of the first $n$ primes).

**Fortune's Conjecture** asserts that every Fortunate number is prime — equivalently,
that no Fortunate number is composite.

The conjecture is named after the social anthropologist Reo Fortune, who proposed it.
The first few Fortunate numbers are $3, 5, 7, 13, 23, 17, 19, 23, 37, 61, \ldots$
(OEIS A005235); all known values are prime.

*References:*

- [Wikipedia](https://en.wikipedia.org/wiki/Fortunate_number)
- [OEIS A005235](https://oeis.org/A005235)
- [PrimePages glossary entry](https://primes.utm.edu/glossary/xpage/FortunateNumber.html)
- [PlanetMath: Fortune's conjecture](https://planetmath.org/fortunesconjecture)
-/

namespace FortuneConjecture

open Nat

/-- The $n$-th *Fortunate number*: the smallest integer $m > 1$ such that
$\mathrm{primorial}(n) + m$ is prime. -/
noncomputable def fortunateNumber (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ Nat.Prime (primorial n + m)}

/-- **Fortune's Conjecture**: Every Fortunate number is prime. -/
@[category research open, AMS 11]
theorem fortune_conjecture :
    (∀ n : ℕ, Nat.Prime (fortunateNumber n)) ↔ answer(sorry) := by
  sorry

end FortuneConjecture