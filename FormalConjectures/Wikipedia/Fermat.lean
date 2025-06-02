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
# Some conjectures about Fermat numbers

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Fermat_number)
-/

/--
All Fermat numbers `n > 4` are composite.
-/
@[category research open]
theorem fermat_number_are_composite (n : ℕ) (hn : n ≥ 4) :
  ¬Prime n.fermatNumber := by
  sorry

/--
There are infinitely many Fermat primes.
-/
@[category research open]
theorem infinite_fermat_primes :
  Infinite {n : ℕ | Prime n.fermatNumber} := by
  sorry

/--
There are infinitely many composite Fermat numbers.
-/
@[category research open]
theorem infinite_fermat_composite :
  Infinite {n : ℕ | ¬Prime n.fermatNumber} := by
  sorry

/--
There is a Fermat number that is not square-free.
-/
@[category research open]
theorem exists_non_squarefree_fermat_number :
  ∃ n : ℕ, ¬Squarefree n.fermatNumber := by
  sorry
