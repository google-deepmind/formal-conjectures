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

import FormalConjecturesUtil

/-!
# Erdős Problem 646

*References:*
- [erdosproblems.com/646](https://www.erdosproblems.com/646)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Be97] Berend, Daniel, *On the parity of exponents in the factorization of $n!$*.
  J. Number Theory (1997), 13-19.
-/

open scoped Nat

namespace Erdos646

/--
Let $p_1,\ldots,p_k$ be distinct primes. Are there infinitely many $n$ such that $n!$ is
divisible by an even power of each of the $p_i$?

The answer is yes, proved by Berend [Be97], who further proved that the sequence of such $n$
has bounded gaps (where the bound depends on the initial set of primes).

The distinct primes $p_1, \ldots, p_k$ are packaged as a finite set of primes, and "$n!$ is
divisible by an even power of $p_i$" is formalized as in [Be97]: the exponent of $p_i$ in the
prime factorization of $n!$ (that is, `padicValNat p (n !)`) is even.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos646.lean"]
theorem erdos_646 : answer(True) ↔
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      {n : ℕ | ∀ p ∈ S, Even (padicValNat p (n !))}.Infinite := by
  sorry

end Erdos646
