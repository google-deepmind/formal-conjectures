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
# Erdős Problem 867

*Reference:* [erdosproblems.com/867](https://www.erdosproblems.com/867)

Erdős asked whether a consecutive-sum-free subset of $\{1, \ldots, N\}$ can have at most
$N/2 + C$ elements for some absolute constant $C$. This was disproved by Coppersmith and Phillips.

[Er92c] Erdős, P., _Some of my favourite problems which recently have been solved_. Proceedings
of the international conference on set-theoretic topology and its applications, Part 2, Matsuyama
(1992).

[CoPh96] Coppersmith, D. and Phillips, S., _Sums along the rationals_. Preprint (1996).
-/

open Finset

namespace Erdos867

/-- A finite set $A$ of natural numbers is "consecutive-sum-free" if, when its
elements are listed in increasing order as $a_1 < a_2 < \cdots < a_t$, no sum of
two or more consecutive elements ($a_i + a_{i+1} + \cdots + a_j$ with $i < j$)
lies in $A$. -/
def ConsecutiveSumFree (A : Finset ℕ) : Prop :=
  let s := A.sort (· ≤ ·)
  ∀ i j : ℕ, i < j → j < s.length →
    (∑ k ∈ Finset.Icc i j, s.getD k 0) ∉ A

/--
Erdős Problem 867 (disproved) [Er92c]:

Is it true that if $A = \{a_1 < \cdots < a_t\} \subseteq \{1, \ldots, N\}$ has no sum of two or
more consecutive elements in $A$, then $|A| \le N/2 + C$ for some absolute constant $C$?

Disproved by Coppersmith and Phillips [CoPh96], who proved the maximum $|A|$ satisfies
$$
  \frac{13}{24} N - O(1) \le |A| \le \left(\frac{2}{3} - \frac{1}{512}\right) N + \log N.
$$
-/
@[category research solved, AMS 5 11]
theorem erdos_867 : answer(False) ↔
    ∃ C : ℕ, ∀ N : ℕ, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
    ConsecutiveSumFree A →
    A.card ≤ N / 2 + C := by
  sorry

end Erdos867
