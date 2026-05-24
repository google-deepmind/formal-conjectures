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
# Green's Open Problem 44

*References:*
- [Gr24] [Ben Green's 100 Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.44)
- [Er80] Erdős, Paul. "A survey of problems in combinatorial number theory."
  Annals of Discrete Mathematics 6 (1980): 89-115.
-/

namespace Green44

open scoped Nat

/--
Sieve $[N]$ by removing half the residue classes mod $p_i$, for primes
$2 \leqslant p_1 < p_2 < \dots < p_{1000} < N^{9/10}$. Does the remaining set have size at most
$\frac{1}{10} N$?

We interpret "half the residue classes" as $\lfloor p_i / 2 \rfloor$.
-/
@[category research open, AMS 11]
theorem green_44 :
    answer(sorry) ↔ ∀ (N : ℕ) (p : Fin 1000 → ℕ) (A : (i : Fin 1000) → Finset (ZMod (p i))),
      let remaining := (Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)
      (∀ i, (p i).Prime) →
      StrictMono p →
      (p 999) ^ 10 < N ^ 9 →
      (∀ i, (A i).card = (p i) / 2) →
      10 * remaining.card ≤ N := by
  sorry

/-- The answer is affirmative if the primes are all less than $N^{1/2}$, by the large sieve. [Gr24] -/
@[category research solved, AMS 11]
theorem green_44.variants.less_than_sqrt :
    ∀ (N : ℕ) (p : Fin 1000 → ℕ) (A : (i : Fin 1000) → Finset (ZMod (p i))),
      let remaining := (Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)
      (∀ i, (p i).Prime) →
      StrictMono p →
      (p 999) ^ 2 < N →
      (∀ i, (A i).card = (p i) / 2) →
      10 * remaining.card ≤ N := by
  sorry

end Green44
