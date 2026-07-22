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
# Erdős Problem 862

*References:*
- [erdosproblems.com/862](https://www.erdosproblems.com/862)
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*. Hardy-Ramanujan J. (1992),
  34-50.
- [SaTh15] Saxton, David and Thomason, Andrew, *Hypergraph containers*. Invent. Math. (2015),
  925-992.
-/

open Finset Filter

open scoped Classical

namespace Erdos862

/--
$A_1(N)$, the number of maximal Sidon subsets of $\{1, \dots, N\}$.
-/
noncomputable def numMaximalSidonSets (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter fun A : Finset ℕ ↦ Set.IsMaximalSidonSetIn (A : Set ℕ) N).card

/--
Let $A_1(N)$ be the number of maximal Sidon subsets of $\{1,\ldots,N\}$. Is it true that
\[A_1(N) < 2^{o(N^{1/2})}?\]

A problem of Cameron and Erdős. This is resolved as a consequence of results of Saxton and
Thomason [SaTh15] - they prove that the number of Sidon sets in $\{1,\ldots,N\}$ is at least
$2^{(1.16+o(1))N^{1/2}}$. Since each Sidon set is contained in a maximal Sidon set, and each
maximal Sidon set contains at most $2^{(1+o(1))N^{1/2}}$ Sidon sets, it follows that
\[A_1(N) \geq 2^{(0.16+o(1))N^{1/2}}.\]
-/
@[category research solved, AMS 5 11]
theorem erdos_862.parts.i : answer(False) ↔
    (fun N : ℕ => Real.logb 2 (numMaximalSidonSets N : ℝ)) =o[atTop]
      (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) := by
  sorry

/--
Let $A_1(N)$ be the number of maximal Sidon subsets of $\{1,\ldots,N\}$. Is it true that
\[A_1(N) > 2^{N^c}\]for some constant $c>0$?

A problem of Cameron and Erdős. This is resolved as a consequence of results of Saxton and
Thomason [SaTh15] - they prove that the number of Sidon sets in $\{1,\ldots,N\}$ is at least
$2^{(1.16+o(1))N^{1/2}}$. Since each Sidon set is contained in a maximal Sidon set, and each
maximal Sidon set contains at most $2^{(1+o(1))N^{1/2}}$ Sidon sets, it follows that
\[A_1(N) \geq 2^{(0.16+o(1))N^{1/2}}.\]
-/
@[category research solved, AMS 5 11]
theorem erdos_862.parts.ii : answer(True) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ ((N : ℝ) ^ c) < (numMaximalSidonSets N : ℝ) := by
  sorry

/--
This is resolved as a consequence of results of Saxton and Thomason [SaTh15] - they prove that
the number of Sidon sets in $\{1,\ldots,N\}$ is at least $2^{(1.16+o(1))N^{1/2}}$. Since each
Sidon set is contained in a maximal Sidon set, and each maximal Sidon set contains at most
$2^{(1+o(1))N^{1/2}}$ Sidon sets, it follows that
\[A_1(N) \geq 2^{(0.16+o(1))N^{1/2}}.\]
-/
@[category research solved, AMS 5 11]
theorem erdos_862.variants.lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ (((0.16 : ℝ) - ε) * (N : ℝ) ^ (1 / 2 : ℝ)) ≤ (numMaximalSidonSets N : ℝ) := by
  sorry

end Erdos862
