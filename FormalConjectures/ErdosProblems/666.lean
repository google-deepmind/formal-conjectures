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
# Erdős Problem 666

*References:*
- [erdosproblems.com/666](https://www.erdosproblems.com/666)
- [BDT93] Brouwer, A. E. and Dejter, I. J. and Thomassen, C., *Highly symmetric subgraphs of
  hypercubes*. J. Algebraic Combin. (1993), 25-29.
- [Ch92] Chung, Fan R. K., *Subgraphs of a hypercube containing no small even cycles*. J. Graph
  Theory (1992), 273-286.
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
-/

open Filter SimpleGraph

open scoped Finset

namespace Erdos666

/-- $Q_n$ is the $n$-dimensional hypercube graph: the vertices are the $n$-bit vectors, and two
vertices are adjacent when they differ in exactly one coordinate. It has $2^n$ vertices and
$n2^{n-1}$ edges. -/
def Q (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := #{i | u i ≠ v i} = 1
  symm _ _ := by simp [eq_comm]
  loopless _ := by simp

/--
Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and $n2^{n-1}$
edges). Is it true that, for every $\epsilon>0$, if $n$ is sufficiently large, every subgraph of
$Q_n$ with
\[\geq \epsilon  n2^{n-1}\]
many edges contains a $C_6$?

The answer to this problem is no: Chung [Ch92] and Brouwer, Dejter, and Thomassen [BDT93]
constructed an edge-partition of $Q_n$ into four subgraphs, each containing no $C_6$.
-/
@[category research solved, AMS 5]
theorem erdos_666 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ H : SimpleGraph (Fin n → Bool), H ≤ Q n →
      ε * n * 2 ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ) → (cycleGraph 6 ⊑ H) := by
  sorry

end Erdos666
