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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 53

*References:*
- [erdosproblems.com/53](https://www.erdosproblems.com/53)
- [Er77c] Erdős, Paul, *Problems and results on combinatorial number theory. III*. Number theory
  day (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [ErSz83] Erdős, P. and Szemerédi, E., *On sums and products of integers*. Studies in pure
  mathematics (1983), 213-218.
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [Er97] Erdős, Paul, *Problems in number theory*. New Zealand J. Math. (1997), 155-160.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Ch03] Chang, M.-C., *The Erdős-Szemerédi problem on sum set and product set*. Annals of Math.
  (2003), 939-957.
-/

@[expose] public section

namespace Erdos53

/-- The integers which are either the sum or the product of (one or more) distinct elements of
`A`. -/
def sumsAndProducts (A : Finset ℤ) : Finset ℤ :=
  (A.powerset.erase ∅).image (fun B => ∑ b ∈ B, b) ∪
    (A.powerset.erase ∅).image (fun B => ∏ b ∈ B, b)

/--
Let $A$ be a finite set of integers. Is it true that, for every $k$, if $\lvert A\rvert$ is
sufficiently large depending on $k$, then there are least $\lvert A\rvert^k$ many integers which
are either the sum or product of distinct elements of $A$?

Asked by Erdős and Szemerédi [ErSz83]. Solved in this form by Chang [Ch03].

Erdős and Szemerédi proved that there exist arbitrarily large sets $A$ such that the number of
integers which are the sum or product of distinct elements of $A$ is at most
$$\exp\left(c (\log \lvert A\rvert)^2\log\log\lvert A\rvert\right)$$
for some constant $c>0$.

See also [52](https://www.erdosproblems.com/52).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos53.lean#L3084"]
theorem erdos_53 : answer(True) ↔ ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
    A.card ^ k ≤ (sumsAndProducts A).card := by
  sorry

/--
Erdős and Szemerédi [ErSz83] proved that there exist arbitrarily large sets $A$ such that the
number of integers which are the sum or product of distinct elements of $A$ is at most
$$\exp\left(c (\log \lvert A\rvert)^2\log\log\lvert A\rvert\right)$$
for some constant $c>0$.
-/
@[category research solved, AMS 11]
theorem erdos_53.variants.upper : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ A : Finset ℤ, N ≤ A.card ∧
    ((sumsAndProducts A).card : ℝ) ≤
      Real.exp (c * Real.log A.card ^ 2 * Real.log (Real.log A.card)) := by
  sorry

end Erdos53
