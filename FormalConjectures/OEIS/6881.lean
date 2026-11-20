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
module

public import FormalConjecturesUtil

/-!
# Squarefree semiprimes

Numbers that are the product of two distinct primes.

References:
- [A006881](https://oeis.org/A006881)
-/

@[expose] public section

namespace OeisA6881

/--
"Conjecture: The sums of two elements of [the sequence of squarefree semiprimes] forms a set that includes all primes greater than
or equal to 29 and all integers greater than or equal to 83 (and many below 83)."
- Richard R. Forberg, Mar 04 2015, [A006881](https://oeis.org/A006881)
-/
@[category research open, AMS 11]
theorem conjecture (k : ℕ) (hk : (29 ≤ k ∧ k.Prime) ∨ (83 ≤ k)) :
    ∃ m n : ({n | n.IsSemiprime ∧ Squarefree n} : Set ℕ), k = m + n := by
  sorry

end OeisA6881
