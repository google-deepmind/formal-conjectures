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
# Kagey Problem 13

For a positive integer $n$, OEIS A261865 is the least positive integer $k$ for
which a positive integer multiple of $\sqrt{k}$ lies strictly between $n$ and
$n + 1$.

For every squarefree $j \geq 2$, the set of positive indices where the sequence
has value $j$ has natural density

$$
\frac{1}{\sqrt{j}}
\prod_{\substack{2 \leq s < j \\ s\text{ squarefree}}}
\left(1 - \frac{1}{\sqrt{s}}\right).
$$

The proof converts the interval-hitting conditions into terminal arcs for a
finite torus rotation. Rational independence of the reciprocal square roots
and multidimensional Weyl equidistribution then reduce the density to the Haar
measure of the corresponding terminal box.

*References:*
- [Peter Kagey, Problem 13](https://peterkagey.com/problems/013/)
- [OEIS A261865](https://oeis.org/A261865)
-/

open Filter
open scoped BigOperators

namespace OeisA261865

/-- A positive integer multiple of $\sqrt{k}$ lies strictly in $(n, n + 1)$. -/
def Hits (k n : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    (n : ℝ) < (m : ℝ) * Real.sqrt (k : ℝ) ∧
      (m : ℝ) * Real.sqrt (k : ℝ) < (n : ℝ) + 1

/-- $k$ is the least positive radicand that hits $(n, n + 1)$. -/
def IsValue (n k : ℕ) : Prop :=
  0 < k ∧ Hits k n ∧ ∀ r : ℕ, 0 < r → r < k → ¬ Hits r n

/-- The predicted density for the value $j$ in OEIS A261865. -/
noncomputable def predictedDensity (j : ℕ) : ℝ :=
  (1 / Real.sqrt (j : ℝ)) *
    ∏ s ∈ (Finset.Ico 2 j).filter Squarefree,
      (1 - 1 / Real.sqrt (s : ℝ))

/--
For every squarefree $j \geq 2$, the positive indices where $j$ is the least
successful radicand have the predicted natural density.
-/
@[category research open, AMS 11]
theorem density_formula (j : ℕ) (hj : 2 ≤ j) (hsq : Squarefree j) :
    {n : ℕ | 0 < n ∧ IsValue n j}.HasDensity (predictedDensity j) := by
  sorry

end OeisA261865
