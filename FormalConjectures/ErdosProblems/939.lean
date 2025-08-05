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
# Erdős Problem 939

*Reference:* [erdosproblems.com/939](https://www.erdosproblems.com/939)
-/
open Nat

/--
A set `S` belongs to `Erdos939Sums r` if it meets the following criteria:
- The size of the set is `$|S| = r - 2$`.
- The elements of the set are coprime (their greatest common divisor is 1).
- Every element in `S` is an `$r$-powerful` number.
- The sum of the elements in `S`, i.e., `$\sum_{s \in S} s$`, is also an `$r$-powerful` number.
-/
def Erdos939Sums (r : ℕ) :=
    {S : Finset ℕ | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧ ∀ s ∈ S, r.Full s}

/--
If $r≥4$ then can the sum of $r-2$ coprime $r$-powerful numbers ever be itself $r$-powerful?
-/
@[category research open, AMS 11]
theorem erdos_939 : (∀ r ≥ 4, (Erdos939Sums r).Nonempty) ↔ answer(sorry) := by
  sorry

/--
If $r≥4$ are there infinitely many sums of $r-2$ coprime $r$-powerful numbers
that are themselves $r$-powerful?
-/
@[category research open, AMS 11]
theorem erdos_939.variants.infinite : (∀ r ≥ 4, (Erdos939Sums r).Infinite) ↔ answer(sorry) := by
  sorry

/--
Are there infinitely many triples of coprime $3$-powerful numbers $a, b, c$ such that $a + b = c$?
-/
@[category research open, AMS 11]
theorem erdos_939.variants.triples :
    {(a,b,c) | ({a, b, c} : Finset ℕ).Coprime ∧
    (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
    a + b = c}.Infinite ↔ answer(sorry) := by sorry

/--
Cambie has found several examples of the sum of $r - 2$ coprime $r$-powerful numbers being itself
$r$-powerful. For example when $r=5$ we have
$$3761^5=2^8\cdot3^{10}\cdot 5^7 + 2^{12}\cdot 23^6 + 11^5\cdot 13^5$$.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.examples : (∃ r ≥ 4, (Erdos939Sums r).Nonempty) := by
  use 5
  simp only [ge_iff_le, reduceLeDiff, true_and]
  unfold Erdos939Sums
  simp [Set.Nonempty]
  use {2^8 * 3^10 * 5^7, 2^12 * 23^6, 11^5 * 13^5}
  simp
  sorry
  /-
  The following proof works in princicple, but throws a "(kernel) deep recursion detected" error,
  caused by the simproc `primeFactorsEq`.

  constructor
  · unfold Finset.Coprime
    aesop
  · simp only [Full, primeFactorsEq, Finset.mem_insert, insert_emptyc_eq, Finset.mem_singleton,
    forall_eq_or_imp, reducePow, forall_eq]
    norm_num
  -/


/-- Cambie has also found solutions when $r=7$.-/
@[category research solved, AMS 11]
theorem erdos_939.variants.seven : (Erdos939Sums 7).Nonempty := by
  sorry

/-- Cambie has also found solutions when $r=8$.-/
@[category research solved, AMS 11]
theorem erdos_939.variants.eight : (Erdos939Sums 8).Nonempty := by
  sorry

/--
Euler had conjectured that the sum of $k - 1$ many $k$-th powers is never a
$k$-th power, but this is false for $k=5$, as Lander and Parkin [LaPa67] found
$$27^5+84^5+110^5+133^5=144^5$$.

[LaPa67] Lander, L. J. and Parkin, T. R., "A counterexample to Euler's sum of powers conjecture."
  Math. Comp. (1967), 101--103.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.euler : ¬ (∀ k ≥ 4, ∀ S : Finset ℕ, S.card = k - 1 →
    ¬ (∃ q, ∑ s ∈ S, s ^ k = q ^k)) := by
  push_neg
  use 5
  norm_num
  use {27, 84, 110, 133}
  constructor
  · decide
  · use 144
    norm_num
