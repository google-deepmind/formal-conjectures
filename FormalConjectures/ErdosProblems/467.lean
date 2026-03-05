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
# Erdős Problem 467

For all sufficiently large $x$, there exists a choice of congruence classes $a_p$ for every prime
$p \leq x$, and a partition of the primes $\leq x$ into two non-empty sets, such that every
$n < x$ is covered by some prime from each part.

*Reference:* [erdosproblems.com/467](https://www.erdosproblems.com/467)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980), p. 93.
-/

namespace Erdos467

/--
Erdős Problem #467 [ErGr80, p. 93]:

For all sufficiently large $x$, there exists a choice of congruence classes
$a_p$ for every prime $p \leq x$, and a decomposition of the set of primes
$\leq x$ into two non-empty sets $A$ and $B$, such that for every $n < x$,
there exist some $p \in A$ and $q \in B$ with $n \equiv a_p \pmod{p}$ and
$n \equiv a_q \pmod{q}$.

The note on the website indicates the original source [ErGr80] is ambiguous
about the quantifiers; this formalises the most natural interpretation.
-/
@[category research open, AMS 5 11]
theorem erdos_467 :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      ∃ (a : ℕ → ℕ) (A : Finset ℕ),
        let P := (Finset.range (x + 1)).filter Nat.Prime
        A ⊆ P ∧
        A.Nonempty ∧
        (P \ A).Nonempty ∧
        ∀ n : ℕ, n < x →
          (∃ p ∈ A, n % p = a p % p) ∧
          (∃ q ∈ P \ A, n % q = a q % q) := by
  sorry

end Erdos467
