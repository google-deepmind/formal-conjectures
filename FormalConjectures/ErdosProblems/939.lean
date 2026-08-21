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

import FormalConjecturesUtil

/-!
# Erdős Problem 939

*References:*
- [erdosproblems.com/939](https://www.erdosproblems.com/939)
- [Ni95] Nitaj, A., _On a conjecture of Erdős on 3-powerful numbers_. Bull. London Math. Soc.
  (1995), 317-318.
- [Co98] Cohn, J. H. E., _A conjecture of Erdős on 3-powerful numbers_. Math. Comp. (1998),
  439-440.
- [Wa24] Walsh, P., _A question of Erdős on 3-powerful numbers and an elliptic curve analogue
  of the Ankeny-Artin-Chowla conjecture_. arXiv:2404.03970 (2024).
- [LaPa67] Lander, L. J. and Parkin, T. R., _A counterexample to Euler's sum of powers
  conjecture_. Math. Comp. (1967), 101-103.
-/
open Nat

namespace Erdos939

/--
A set `S` belongs to `Erdos939Sums r` if it meets the following criteria:
- The elements are positive. `0` has no prime factors, so it is vacuously `r`-powerful, and
  the source means positive integers.
- The size of the set is `$|S| = r - 2$`.
- The elements of the set are coprime (their greatest common divisor is 1).
- Every element in `S` is an `$r$-powerful` number.
- The sum of the elements in `S`, i.e., `$\sum_{s \in S} s$`, is also an `$r$-powerful` number.
-/
def Erdos939Sums (r : ℕ) :=
    {S : Finset ℕ | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧
      ∀ s ∈ S, 0 < s ∧ r.Full s}

/--
If $r≥4$ then can the sum of $r-2$ coprime $r$-powerful numbers ever be itself $r$-powerful?
-/
@[category research open, AMS 11]
theorem erdos_939 : answer(sorry) ↔ ∀ r ≥ 4, (Erdos939Sums r).Nonempty := by
  sorry

/--
If $r≥4$ are there infinitely many sums of $r-2$ coprime $r$-powerful numbers
that are themselves $r$-powerful?

A construction in the site's comments, from GPT-5.5 Pro prompted by Price, gives infinitely
many for every $r \ge 6$. This statement quantifies over every $r \ge 4$, so it stays open at
$r = 4$ and $r = 5$. The category is unchanged because the construction is recorded in the
comments and not in the literature.
-/
@[category research open, AMS 11]
theorem erdos_939.variants.infinite : answer(sorry) ↔ ∀ r ≥ 4, (Erdos939Sums r).Infinite := by
  sorry

/--
Are there infinitely many triples of coprime $3$-powerful numbers $a, b, c$ such that $a + b = c$?

The answer is yes. Nitaj [Ni95] proved it, with $2^3\cdot 3^5\cdot 73^3 + 271^3 = 919^3$ as an
example. In Nitaj's construction at least two of $a, b, c$ are perfect cubes. Cohn [Co98]
constructed infinitely many triples of which none is a perfect cube, and Walsh [Wa24] gave a
further construction.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.triples :
    answer(True) ↔ {(a,b,c) | ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      a + b = c}.Infinite := by
  sorry

/--
Cambie has found several examples of the sum of $r - 2$ coprime $r$-powerful numbers being itself
$r$-powerful. For example when $r=5$ we have
$$3^7\cdot 61^5 = 2^8\cdot3^{10}\cdot 5^7 + 2^{12}\cdot 23^6 + 11^5\cdot 13^5$$.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.examples : (∃ r ≥ 4, (Erdos939Sums r).Nonempty) := by
  use 5
  simp only [ge_iff_le, reduceLeDiff, true_and]
  unfold Erdos939Sums
  simp [Set.Nonempty]
  use {2^8 * 3^10 * 5^7, 2^12 * 23^6, 11^5 * 13^5}
  simp
  constructor
  · unfold Finset.Coprime
    aesop
  · norm_num [Nat.Full, Nat.primeFactors, Nat.primeFactorsList]


/-- Cambie has also found solutions when $r=7$. -/
@[category research solved, AMS 11]
theorem erdos_939.variants.seven : (Erdos939Sums 7).Nonempty := by
  sorry

/--
Cambie has also found solutions when $r=8$.

The source adds that the $r=8$ solution works "even with the sum of $5$ $8$-powerful numbers".
That is a stronger result than this statement, which asks for the $r - 2 = 6$ summands of
`Erdos939Sums`.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.eight : (Erdos939Sums 8).Nonempty := by
  sorry

/--
Euler had conjectured that the sum of $k - 1$ many $k$-th powers is never a
$k$-th power, but this is false for $k=5$, as Lander and Parkin [LaPa67] found
$$27^5+84^5+110^5+133^5=144^5$$.

The summands must be positive. Without that condition a set containing `0` would count, so the
negation would be satisfied by a sum of fewer than $k-1$ powers and would claim less than the
refutation of Euler's conjecture that this theorem records.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.euler : ¬ (∀ k ≥ 4, ∀ S : Finset ℕ, S.card = k - 1 →
    (∀ s ∈ S, 0 < s) → ¬ (∃ q, ∑ s ∈ S, s ^ k = q ^k)) := by
  push_neg
  use 5
  norm_num
  use {27, 84, 110, 133}
  refine ⟨by decide, by decide, 144, by norm_num⟩

end Erdos939
