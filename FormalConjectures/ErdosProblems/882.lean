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
# Erdős Problem 882

*References:*
- [erdosproblems.com/882](https://www.erdosproblems.com/882)
- [Er98] Erdős, Paul, *Some of my new and almost new problems and results in combinatorial
  number theory*. Number theory (Eger, 1996) (1998), 169-180.
- [ELRSS99] Erdős, P., Lev, V., Rauzy, G., Sándor, C. and Sárközy, A., *Greedy algorithm,
  arithmetic progressions, subset sums and divisibility*. Discrete Math. (1999), 119-135.
- [Erdős Problem 1](https://www.erdosproblems.com/1) for the upper bound.
- [Alexeev] Boris Alexeev's sorry-free Lean 4 formalisation of the lower bound,
  [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos882.lean).
-/

@[expose] public section

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
    Filter.Tendsto (fun n : ℕ => (maxAntichainCard n : ℝ) / Real.logb 2 n)
      Filter.atTop (nhds 1) := by
  sorry

/--
The construction of [ELRSS99]: $A_m = \{2^m - 2^i : 0 \leq i < m\}$.
-/
def A (m : ℕ) : Finset ℕ := (Finset.range m).image (fun i => 2 ^ m - 2 ^ i)

/-- `A m` is contained in `{1, ..., 2^m - 1}`. -/
@[category test, AMS 5 11]
theorem A_subset_Icc (m : ℕ) : A m ⊆ Finset.Icc 1 (2 ^ m - 1) := by
  intro a ha
  simp only [A, Finset.mem_image, Finset.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  have h1 : 2 ^ i < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hi
  have h2 : 0 < 2 ^ i := by positivity
  rw [Finset.mem_Icc]
  omega

/-- `A m` has `m` elements: the map $i \mapsto 2^m - 2^i$ is injective on $\{0, \ldots, m-1\}$. -/
@[category test, AMS 5 11]
theorem card_A (m : ℕ) : (A m).card = m := by
  rw [A, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  have hi' : 2 ^ i < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp (Finset.mem_coe.mp hi))
  have hj' : 2 ^ j < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp (Finset.mem_coe.mp hj))
  have h : 2 ^ m - 2 ^ i = 2 ^ m - 2 ^ j := hij
  have h' : 2 ^ i = 2 ^ j := by omega
  exact Nat.pow_right_injective le_rfl h'

/--
Erdős, Lev, Rauzy, Sándor and Sárközy [ELRSS99] proved that
$\lvert A\rvert > \log_2 n - 1$ is achievable, taking
$A = \{2^m - 2^{m-1}, 2^m - 2^{m-2}, \ldots, 2^m - 1\}$.

The key property of this construction is that distinct nonempty subsets have subset sums
which never divide one another.

The linked theorem `no_div` is phrased in terms of index sets $S \subseteq \{0, \ldots, m-1\}$,
i.e. $\sum_{i \in S_1} (2^m - 2^i) \nmid \sum_{i \in S_2} (2^m - 2^i)$ for distinct nonempty
$S_1, S_2$; it transfers to subsets of `A m` via the injectivity of $i \mapsto 2^m - 2^i$
(see `card_A`).
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/ToshiDad/erdos-882/blob/6ea233aed4b3efce92e2754177ef15c4085f8732/Erdos882.lean#L394"]
theorem erdos_882.variants.lower_bound (m : ℕ) : IsSubsetSumAntichain (A m) := by
  sorry

/--
The lower bound of [ELRSS99] in quantitative form: for every $n \geq 1$ there is a subset-sum
antichain $A \subseteq \{1, \ldots, n\}$ with $\lvert A\rvert > \log_2 n - 1$, namely $A_m$
with $m = \lfloor \log_2 n \rfloor$ (by `erdos_882.variants.lower_bound`, `A_subset_Icc`
and `card_A`).

A sorry-free Lean 4 proof of this statement is the theorem `erdos_882` of [Alexeev].
That formalisation expresses the antichain condition as primitivity of the *set* of nonempty
subset sums (no element divides another one). For $A \subseteq \{1, \ldots, n\}$ this is
equivalent to `IsSubsetSumAntichain A`: if two distinct subsets had the same sum, then
removing their common elements would leave two disjoint nonempty subsets with a common sum
$t \geq 1$, so that $t$ and $2t$ would both be nonempty subset sums.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos882.lean#L561"]
theorem erdos_882.variants.lower_bound_explicit (n : ℕ) (hn : 0 < n) :
    Real.logb 2 n - 1 < (maxAntichainCard n : ℝ) := by
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
    ∀ᶠ n : ℕ in Filter.atTop, (Real.logb 3 n - 1 : ℝ) ≤ (maxAntichainCard n : ℝ) := by
  sorry

end Erdos882
