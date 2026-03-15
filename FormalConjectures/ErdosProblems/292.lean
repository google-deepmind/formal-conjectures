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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 292

*Reference:* [erdosproblems.com/292](https://www.erdosproblems.com/292)

Does the set of positive integers that can appear as the largest denominator in an
Egyptian fraction representation of 1 have natural density 1?

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).

[Ma00] Martin, G., *Dense Egyptian fractions*. Trans. Amer. Math. Soc. 351 (1999),
3641–3657.
-/

open Classical

namespace Erdos292

/-- A positive integer $n$ is Egyptian representable if there exists a finite set
of distinct positive integers with maximum element $n$ whose reciprocals sum to $1$.
That is, there exist $1 \leq m_1 < \cdots < m_k = n$ with $\sum 1/m_i = 1$. -/
def IsEgyptianRepresentable (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, n ∈ S ∧ (∀ m ∈ S, 1 ≤ m) ∧ (∀ m ∈ S, m ≤ n) ∧
    (S.sum fun m => (1 : ℚ) / m) = 1

/--
Erdős Problem 292 (Proved) [ErGr80, p.35]:

Does the set of positive integers $n$ for which there exist $1 \leq m_1 < \cdots < m_k = n$
with $\sum 1/m_i = 1$ have natural density $1$?

Proved by Martin [Ma00], who showed the complementary set $B = \mathbb{N} \setminus A$ satisfies
$|B \cap [1,x]| / x \asymp \log \log x / \log x$.
-/
@[category research solved, AMS 11]
theorem erdos_292 : answer(True) ↔
    {n : ℕ | IsEgyptianRepresentable n}.HasDensity 1 := by
  sorry

end Erdos292
