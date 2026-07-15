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
# Erdős Problem 453

*References:*
- [erdosproblems.com/453](https://www.erdosproblems.com/453)
- [Er70b] Erdős, P., *Some applications of graph theory to number theory*. Proc. Second Chapel Hill
  Conf. on Combinatorial Mathematics and its Applications (Univ. North Carolina, Chapel Hill, N.C.,
  1970) (1970), 136-145.
- [Er74b] Erdős, P., *Remarks on some problems in number theory*. Math. Balkanica (1974), 197-202.
- [Er77c] Erdős, Paul, *Problems and results on combinatorial number theory. III*. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
- [Po79] Pomerance, Carl, *The prime number graph*. Math. Comp. (1979), 399-408.
-/

namespace Erdos453

/-- The eventual prime inequality asked in Erdős Problem 453, using Mathlib's zero-based primes. -/
def EventuallyHasPrimeWitness : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ i : ℕ, i < n ∧
      (Nat.nth Nat.Prime n) ^ (2 : ℕ) <
        Nat.nth Nat.Prime (n + i) * Nat.nth Nat.Prime (n - i)

/--
Is it true that, for all sufficiently large $n$, there exists some $i<n$ such that
\[
p_n^2 < p_{n+i}p_{n-i},
\]
where $p_k$ is the $k$th prime?

Pomerance proved that the answer is no.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos453.lean"]
theorem erdos_453 : answer(False) ↔ EventuallyHasPrimeWitness := by
  sorry

end Erdos453
