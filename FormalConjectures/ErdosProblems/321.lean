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
# Erdős Problem 321

*References:*
- [erdosproblems.com/320](https://www.erdosproblems.com/320)
- [erdosproblems.com/321](https://www.erdosproblems.com/321)
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [BGMS25] S. Bettin, L. Grenié, G. Molteni, and C. Sanna, A lower bound for the number of Egyptian
  fractions. arXiv:2509.10030 (2025).
- [BlEr75] Bleicher, M. N. and Erdős, P., The number of distinct subsums of $\sum \sb{1}\spN\,1/i$.
  Math. Comp. (1975), 29-42.
- [BlEr76b] Bleicher, Michael N. and Erdős, Paul, Denominators of Egyptian fractions. II. Illinois
  J. Math. (1976), 598-613.
-/

open Filter Real
open scoped Finset

namespace Erdos321

/--
Let $R(N)$ be the size of the largest $A\subseteq\{1, ..., N\}$ such that all sums
$\sum_{n\in S} \frac{1}{n}$ are distinct for $S\subseteq A$.
-/
noncomputable def R (N : ℕ) : ℕ :=
  sSup { #A | (A) (_ : A ⊆ Finset.Icc 1 N)
      (_ : Set.InjOn (fun (S : Finset ℕ) ↦ ∑ n ∈ S, (1 : ℚ) / n) A.powerset) }

/--
Let $S(N)$ be the number of distinct values of $\sum_{n \in A} \frac{1}{n}$ as $A$ ranges over all
subsets of $\{1, ..., N\}$.
-/
noncomputable def S (N : ℕ) : ℕ :=
  #((Finset.Icc 1 N).powerset.image (fun (A : Finset ℕ) ↦ ∑ n ∈ A, (1 : ℚ) / n))

/--
Let $R(N)$ be the size of the largest $A\subseteq\{1, ..., N\}$ such that all sums
$\sum_{n\in S} \frac{1}{n}$ are distinct for $S\subseteq A$. Estimate $R(N)$.

It is now known that $R(N)\asymp \log S(N) \asymp \frac{N}{\log N}\prod_{j=3}^k \log_k N$
where $k$ is such that $\log_kN=O(1)$. The lower bound is implicit in work of Bettin, Grenié,
Molteni, and Sanna [BGMS25].
-/
@[category research solved, AMS 11]
theorem erdos_321.parts.i :
    answer(fun N ↦ N / log N * ∏ j ∈ Finset.Icc 3 (sSup { k | k ≤ log^[k] N }), (log^[j] N)) =O[atTop]
      fun N ↦ (R N : ℝ) := by
  sorry

/--
The upper bound was proved by GPT 5.6 Sol (prompted by Young, Zhu, and Luo) - see
[erdosproblems.com/320] for more details.
-/
@[category research solved, AMS 11]
theorem erdos_321.parts.ii :
    (fun N ↦ (R N : ℝ)) =O[atTop]
      answer(fun N ↦ N / log N * ∏ j ∈ Finset.Icc 3 (sSup { k | k ≤ log^[k] N }), (log^[j] N)) := by
  sorry

/--
Results of Bleicher and Erdős from [BlEr75] and [BlEr76b] imply
that $\frac{N}{\log N}\prod_{i=3}^k\log_iN\leq R(N)\leq \frac{1}{\log 2}\log_r N\left(\frac{N}{\log N}
\prod_{i=3}^r \log_iN\right)$ valid for any $k\geq 4$ with $\log_kN\geq k$ and any $r\geq 1$ with
$\log_{2r}N\geq 1$. (In these bounds $\log_in$ denotes the $i$-fold iterated logarithm.)
-/
@[category research solved, AMS 11]
theorem erdos_321.variants.bleicher_erdos (N k r : ℕ) (hk : 4 ≤ k) (hkN : k ≤ log^[k] N)
    (hr : 1 ≤ r) (hrN : 1 ≤ log^[2 * r] N) :
    N / log N * ∏ i ∈ Finset.Icc 3 k, (log^[i] N) ≤ R N ∧
      R N ≤ 1 / log 2 * log^[r] N * N / log N * ∏ i ∈ Finset.Icc 3 r, (log^[i] N) := by
  sorry

/--
It is trivial that $2^{R(N)}\leq S(N)$, where $S(N)$ is defined in [erdosproblems.com/320].
-/
@[category textbook, AMS 11]
theorem erdos_321.variants.pow_r_le_s (N : ℕ) :
    2 ^ R N ≤ S N := by
  sorry

end Erdos321
