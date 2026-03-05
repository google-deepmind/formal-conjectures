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
# Erdős Problem 1026

*Reference:* [erdosproblems.com/1026](https://www.erdosproblems.com/1026)

Let $x_1, \ldots, x_n$ be a sequence of distinct real numbers. Determine
$\max(\sum x_{i_r})$, where the maximum is taken over all monotonic subsequences.

The precise formulation (van Doorn): What is the largest constant $c$ such that,
for all sequences of $n$ real numbers $x_1, \ldots, x_n$,
$$\max(\sum x_{i_r}) > (c - o(1)) \cdot \frac{1}{\sqrt{n}} \cdot \sum x_i$$
where the maximum is over all monotonic subsequences?

Cambie conjectured the stronger statement: if $x_1, \ldots, x_{k^2}$ are distinct
positive real numbers with $\sum x_i = 1$, then there is always a monotonic
subsequence with sum at least $1/k$. This shows $c = 1$.

This was proved by Tidor, Wang, and Yang [TWY16], and is also implicit in
work of Wagner [Wa17]. It has been formalised in Lean.

[TWY16] Tidor, J., Wang, V., and Yang, K., _Weighted monotone subsequences_ (2016).

[Wa17] Wagner, A. Z. (2017).
-/

open Finset

namespace Erdos1026

/-- A set of indices forms an increasing subsequence of $x$ if for all
pairs of indices in the set, the one with larger index has larger value. -/
def IsIncreasingSubseq {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i < j → x i < x j

/-- A set of indices forms a decreasing subsequence of $x$ if for all
pairs of indices in the set, the one with larger index has smaller value. -/
def IsDecreasingSubseq {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i < j → x i > x j

/-- A set of indices forms a monotone subsequence if it is either
increasing or decreasing. -/
def IsMonotoneSubseq {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  IsIncreasingSubseq x S ∨ IsDecreasingSubseq x S

/--
Erdős Problem 1026 (Cambie's conjecture, proved by Tidor–Wang–Yang [TWY16]):

If $x_1, \ldots, x_{k^2}$ are distinct positive real numbers summing to $1$, then
there exists a monotone subsequence whose sum is at least $1/k$.

This is a weighted form of the Erdős–Szekeres theorem.
-/
@[category research solved, AMS 5]
theorem erdos_1026 (k : ℕ) (hk : k ≥ 1)
    (x : Fin (k ^ 2) → ℝ)
    (hx_pos : ∀ i, x i > 0)
    (hx_inj : Function.Injective x)
    (hx_sum : ∑ i, x i = 1) :
    ∃ S : Finset (Fin (k ^ 2)), IsMonotoneSubseq x S ∧
      ∑ i ∈ S, x i ≥ 1 / (k : ℝ) := by
  sorry

end Erdos1026
