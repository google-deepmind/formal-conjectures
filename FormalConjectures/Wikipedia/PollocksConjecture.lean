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
# Pollock's (tetrahedral numbers) conjecture

Every positive integer is the sum of at most 5 tetrahedral numbers.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Pollock%27s_conjectures)
- [OEIS A000797](https://oeis.org/A000797)
- L. E. Dickson, *History of the Theory of Numbers, Vol. II: Diophantine Analysis*, Dover (2005), pp. 22–23
- Frederick Pollock, *On the extension of the principle of Fermat's theorem on the polygonal numbers to the higher order of series whose ultimate differences are constant*, Abstracts of the Papers Communicated to the Royal Society of London **5** (1850), 922–924
- H. E. Salzer and N. Levine, *Table of integers not exceeding 100000 that are not expressible as the sum of four tetrahedral numbers*, Math. Comp. **12** (1958), 141–144
- [MathWorld: Pollock's Conjecture](https://mathworld.wolfram.com/PollocksConjecture.html)
-/

namespace PollocksConjecture

open scoped BigOperators

/-! ## Definitions -/

/-- The `n`-th tetrahedral number: \(T_n = n (n+1) (n+2) / 6\). -/
def tetrahedral (n : ℕ) : ℕ :=
  n * (n + 1) * (n + 2) / 6

/-! ## Statements -/

/--
Pollock's (tetrahedral numbers) conjecture:
every positive integer is the sum of at most 5 tetrahedral numbers.
-/
@[category research open, AMS 11]
theorem pollock_tetrahedral (N : ℕ) (hN : 0 < N) :
    ∃ f : Fin 5 → ℕ, N = ∑ i, tetrahedral (f i) := by
  sorry

/--
Salzer–Levine strengthening (as stated on Wikipedia/OEIS):
the set of positive integers that are *not* a sum of at most 4 tetrahedral numbers is finite.
-/
@[category research open, AMS 11]
theorem pollock_tetrahedral.finite_exceptions :
    Set.Finite {N : ℕ | 0 < N ∧ ¬ ∃ f : Fin 4 → ℕ, N = ∑ i, tetrahedral (f i)} := by
  sorry

end PollocksConjecture

