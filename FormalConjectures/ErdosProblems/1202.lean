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
# Erdős Problem 1202

*References:*
- [erdosproblems.com/1202](https://www.erdosproblems.com/1202)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [Gr24] [Ben Green's 100 Open Problems, Problem 44](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.44)
-/

@[expose] public section

namespace Erdos1202

set_option linter.style.formal_proof_palomar false in
/--
Let $\epsilon > 0$. Does there exist $k$ such that, for every $n$, any primes
$p_1 < \cdots < p_k < n^{1-\epsilon}$ and any sets $A_i$ of $\frac{p_i - 1}{2}$ residue classes
modulo $p_i$, the number of $m \le n$ that avoid $A_i \pmod{p_i}$ for every $i$ is at most
$\epsilon n$?

The answer is negative: according to [erdosproblems.com/1202](https://www.erdosproblems.com/1202),
Price (with GPT-5.4 Pro) gave a construction in which the $A_i$ are intervals of residues and at
least $(1/2 - c) n$ integers in $[1, n]$ survive. The large sieve gives a positive answer when
$p_k < n^{1/2}$ instead. See also `Green44` for a related special case.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1202.lean"]
theorem erdos_1202 :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ (n : ℕ) (p : Fin k → ℕ) (A : (i : Fin k) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) →
      StrictMono p →
      (∀ i, (p i : ℝ) < (n : ℝ) ^ (1 - ε)) →
      (∀ i, (A i).card = (p i - 1) / 2) →
      ((((Finset.Icc 1 n).filter (fun m => ∀ i, (m : ZMod (p i)) ∉ A i)).card : ℕ) : ℝ) ≤ ε * n := by
  sorry

end Erdos1202
