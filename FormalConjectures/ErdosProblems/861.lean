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

/-- Size of the largest Sidon subset of `{1, …, N}`. -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {n | ∃ A : Set ℕ, A ⊆ Icc 1 N ∧ IsSidon A ∧ A.ncard = n}

/-- Number of Sidon subsets of `{1, …, N}`. -/
noncomputable def Acount (N : ℕ) : ℕ :=
  {S : Set ℕ | S ⊆ Icc 1 N ∧ IsSidon S}.ncard

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

end Erdos861
