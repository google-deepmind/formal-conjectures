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
# Prime numbers at the beginning of the 20th century

The sequence consists of $1$ and the prime numbers. Today $1$ is no longer regarded as a prime.

*References:*
- [A008578](https://oeis.org/A008578)
-/

@[expose] public section

namespace OeisA8578

open ArithmeticFunction

/-- The predicate for the sequence: $n = 1$ or $n$ is prime. -/
def A (n : ℕ) : Prop := n = 1 ∨ n.Prime

@[category test, AMS 11]
theorem a_1 : A 1 := by simp [A]

@[category test, AMS 11]
theorem a_2 : A 2 := by norm_num [A]

@[category test, AMS 11]
theorem a_3 : A 3 := by norm_num [A]

@[category test, AMS 11]
theorem a_5 : A 5 := by norm_num [A]

@[category test, AMS 11]
theorem a_7 : A 7 := by norm_num [A]

/--
"Conjecture: the sequence contains exactly those k such that sigma(k) > k*BigOmega(k)."
- Irina Gerasimova, Jun 08 2013

Here $\sigma(k)$ is the sum of the divisors of $k$ and $\Omega(k)$ is the number of prime factors
of $k$ counted with multiplicity. Both sides are false for $k = 0$.

Solved by Claude (Anthropic) prompted by otoinobuo. The proof shows $\sigma(k) < k P$ for the
largest prime factor $P$ of $k$ and uses induction on $k / P$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/otoi-lab/oeis-lean-proofs/blob/14f275b8b370bcf76213de10bb3f8fda84a6461e/OeisProofs/FC/A8578.lean#L18-L21"]
theorem conjecture (k : ℕ) : A k ↔ k * cardFactors k < sigma 1 k := by
  sorry

end OeisA8578
