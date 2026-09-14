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
# Erdős Problem 861

*References:*
- [erdosproblems.com/861](https://www.erdosproblems.com/861)
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
- [KLRS15] Kohayakawa, Yoshiharu and Lee, Sang June and Rödl, Vojtěch and Samotij, Wojciech,
  *The number of Sidon sets and the maximum size of Sidon sets contained in a sparse random set of
  integers*. Random Structures Algorithms (2015), 1--25.
- [SaTh15] Saxton, David and Thomason, Andrew, *Hypergraph containers*. Invent. Math. (2015),
  925--992.
-/

open Filter Asymptotics Set
open scoped Topology

namespace Erdos861

/-- Size of the largest Sidon subset of `{1, …, N}`. Same API as `erdos_30` / `erdos_43`. -/
noncomputable abbrev f (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)

/-- Number of Sidon subsets of `{1, …, N}`. -/
noncomputable abbrev Acount (N : ℕ) : ℕ := Finset.sidonSubsetCount (Finset.Icc 1 N)

/--
Let $f(N)$ be the size of the largest Sidon subset of $\{1,\ldots,N\}$ and $A(N)$ be the number of
Sidon subsets of $\{1,\ldots,N\}$. Is it true that
$$A(N)/2^{f(N)}\to \infty?$$

A problem of Cameron and Erdős. While $A(N)$ has not been completely determined, this question is
settled in the affirmative.
-/
@[category research solved, AMS 5 11]
theorem erdos_861.parts.i : answer(True) ↔
    Tendsto (fun N : ℕ ↦ (Acount N : ℝ) / (2 : ℝ) ^ f N) atTop atTop := by
  sorry

/--
Is it true that
$$A(N) = 2^{(1+o(1))f(N)}?$$

This is false: the lower bound $A(N)\ge 2^{1.16 f(N)}$ of Saxton and Thomason [SaTh15] already
prevents the exponent $1+o(1)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_861.parts.ii : answer(False) ↔
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ N : ℕ in atTop, (Acount N : ℝ) = (2 : ℝ) ^ ((1 + o N) * f N) := by
  sorry

/--
The current best lower bound (for large $N$) is due to Saxton and Thomason [SaTh15]:
$$2^{1.16 f(N)}\leq A(N).$$
-/
@[category research solved, AMS 5 11]
theorem erdos_861.variants.lower :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ ((1.16 : ℝ) * f N) ≤ Acount N := by
  sorry

/--
The current best upper bound (for large $N$) is due to Kohayakawa, Lee, Rödl, and Samotij
[KLRS15]:
$$A(N)\leq 2^{6.442 f(N)}.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_861.variants.upper :
    ∀ᶠ N : ℕ in atTop, (Acount N : ℝ) ≤ (2 : ℝ) ^ ((6.442 : ℝ) * f N) := by
  sorry

/-- The empty set is Sidon. -/
@[category test, AMS 5 11]
theorem erdos_861.variants.empty_sidon : IsSidon (∅ : Set ℕ) := by
  intro _ h
  cases h

/-- There is always at least one Sidon subset of `{1, …, N}` (the empty set). -/
@[category test, AMS 5 11]
theorem erdos_861.variants.one_le_Acount (N : ℕ) : 1 ≤ Acount N :=
  Finset.one_le_sidonSubsetCount _

/-- Trivial bound underlying the Cameron–Erdős ratio: `2^{f(N)} ≤ A(N)`. -/
@[category test, AMS 5 11]
theorem erdos_861.variants.two_pow_f_le_Acount (N : ℕ) : 2 ^ f N ≤ Acount N :=
  Finset.two_pow_maxSidonSubsetCard_le_sidonSubsetCount _

/-- Trivial size bound: `f(N) ≤ N`. -/
@[category test, AMS 5 11]
theorem erdos_861.variants.f_le_card (N : ℕ) : f N ≤ (Finset.Icc 1 N).card :=
  Finset.maxSidonSubsetCard_le_card _

/-- Trivial count bound: `A(N) ≤ 2^N` (actually `≤ 2^{#(Icc 1 N)}`). -/
@[category test, AMS 5 11]
theorem erdos_861.variants.Acount_le_two_pow (N : ℕ) :
    Acount N ≤ 2 ^ (Finset.Icc 1 N).card :=
  Finset.sidonSubsetCount_le_two_pow_card _

/-- Monotonicity in `N`: larger intervals admit at least as large a Sidon subset. -/
@[category test, AMS 5 11]
theorem erdos_861.variants.f_mono {M N : ℕ} (h : M ≤ N) : f M ≤ f N :=
  Finset.maxSidonSubsetCard_mono (Finset.Icc_subset_Icc_right h)

/-- Monotonicity in `N` for the Sidon-subset count. -/
@[category test, AMS 5 11]
theorem erdos_861.variants.Acount_mono {M N : ℕ} (h : M ≤ N) : Acount M ≤ Acount N :=
  Finset.sidonSubsetCount_mono (Finset.Icc_subset_Icc_right h)


/-- The infinite greedy Sidon sequence has Sidon range. -/
@[category API, AMS 5 11]
theorem erdos_861.variants.isSidon_range_greedySidon :
    IsSidon (Set.range Finset.greedySidon) :=
  Finset.isSidon_range_greedySidon

/-- The greedy Sidon sequence is strictly increasing. -/
@[category API, AMS 5 11]
theorem erdos_861.variants.greedySidon_strictMono :
    StrictMono Finset.greedySidon :=
  Finset.greedySidon.strictMono

/-- Trivial: `greedySidon 0 = 1`. -/
@[category test, AMS 5 11]
theorem erdos_861.variants.greedySidon_zero : Finset.greedySidon 0 = 1 :=
  Finset.greedySidon_zero

end Erdos861
