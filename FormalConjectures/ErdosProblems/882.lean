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
# Erdős Problem 882

*References:*
- [erdosproblems.com/882](https://www.erdosproblems.com/882)
- [Er98] Erdős, Paul, *Some of my new and almost new problems and results in combinatorial
  number theory*. Number theory (Eger, 1996) (1998), 169-180.
- [ELRSS99] Erdős, P., Lev, V., Rauzy, G., Sándor, C. and Sárközy, A., *Greedy algorithm,
  arithmetic progressions, subset sums and divisibility*. Discrete Math. (1999), 119-135.
- [Erdős Problem 1](https://www.erdosproblems.com/1) for the upper bound.
-/

open Finset

namespace Erdos882

/--
A finite set `A` of naturals is *subset-sum antichain* if no two distinct nonempty subsets of
`A` have subset sums dividing one another.
-/
def IsSubsetSumAntichain (A : Finset ℕ) : Prop :=
  ∀ S₁ ⊆ A, ∀ S₂ ⊆ A, S₁.Nonempty → S₂.Nonempty → S₁ ≠ S₂ →
    ¬ (∑ a ∈ S₁, a) ∣ (∑ a ∈ S₂, a)

/-- The largest size of a subset-sum antichain contained in `{1, ..., n}`. -/
noncomputable def maxAntichainCard (n : ℕ) : ℕ :=
  sSup {k | ∃ A ⊆ Finset.Icc 1 n, IsSubsetSumAntichain A ∧ A.card = k}

/--
What is the size of the largest $A\subseteq \{1,\ldots,n\}$ such that in the set
$$\left\{ \sum_{a\in S} a : \emptyset\neq S\subseteq A\right\}$$
no two distinct elements divide each other?

A problem of Erdős and Sárközy. The answer is $(1+o(1))\log_2 n$: the lower bound
$\lvert A\rvert > \log_2 n - 1$ is achieved by the construction of Erdős, Lev, Rauzy, Sándor
and Sárközy [ELRSS99] (see `erdos_882.variants.lower_bound`), while
[Erdős Problem 1](https://www.erdosproblems.com/1) gives
$\lvert A\rvert \leq \log_2 n + \tfrac{1}{2}\log_2\log n + O(1)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_882 :
    (fun n => (maxAntichainCard n : ℝ)) ~[Filter.atTop] (fun n => Real.logb 2 n) := by
  sorry

/--
The construction of [ELRSS99]: $A_m = \{2^m - 2^i : 0 \leq i < m\}$.
-/
def A (m : ℕ) : Finset ℕ := (Finset.range m).image (fun i => 2 ^ m - 2 ^ i)

/-- `A m` is contained in `{1, ..., 2^m - 1}` and has `m` elements. -/
@[category research solved, AMS 5 11]
theorem card_A (m : ℕ) (hm : 1 ≤ m) :
    A m ⊆ Finset.Icc 1 (2 ^ m - 1) ∧ (A m).card = m := by
  sorry

/--
Erdős, Lev, Rauzy, Sándor and Sárközy [ELRSS99] proved that
$\lvert A\rvert > \log_2 n - 1$ is achievable, taking
$A = \{2^m - 2^{m-1}, 2^m - 2^{m-2}, \ldots, 2^m - 1\}$.

The key property of this construction is that distinct nonempty subsets have subset sums
which never divide one another.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/ToshiDad/erdos-882"]
theorem erdos_882.variants.lower_bound (m : ℕ) : IsSubsetSumAntichain (A m) := by
  sorry

/--
Sándor's construction (reported without reference in [Er98]) is claimed to achieve
$\lvert A\rvert = (1-o(1))\log_2 n$ with $A = \{2^i + m 2^m : 0 \leq i < m\}$ and
$n = 2^{m-1} + m 2^m$.
-/
@[category research solved, AMS 5 11]
theorem erdos_882.variants.sandor (m : ℕ) (hm : 1 ≤ m) :
    IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m)) := by
  sorry

/--
The greedy algorithm shows that $\lvert A\rvert \geq (1-o(1))\log_3 n$ is possible.
-/
@[category research solved, AMS 5 11]
theorem erdos_882.variants.greedy :
    ∀ᶠ n in Filter.atTop, (Real.logb 3 n - 1 : ℝ) ≤ maxAntichainCard n := by
  sorry

end Erdos882
