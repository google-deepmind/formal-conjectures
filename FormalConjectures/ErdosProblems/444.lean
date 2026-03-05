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
# Erdős Problem 444

*Reference:* [erdosproblems.com/444](https://www.erdosproblems.com/444)

Let $A \subseteq \mathbb{N}$ be infinite and let $d_A(n)$ count the divisors of $n$ that belong
to $A$. Then for every $k$ the limsup of $\max_{n < x} d_A(n)$ divided by the $k$-th power of
the partial reciprocal sum $\sum_{a \in A,\, a < x} 1/a$ is infinite.

[ErSa80] Erdős, P. and Sárkőzy, A., *On the number of divisors of $n!$*, 1980.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique, 1980.
-/

open Finset Filter BigOperators Classical

namespace Erdos444

/-- $d_A(n)$: the number of elements of $A$ that divide $n$. -/
noncomputable def divisorCountIn (A : Set ℕ) (n : ℕ) : ℕ :=
  (n.divisors.filter (· ∈ A)).card

/-- The partial sum of reciprocals of elements of $A$ in $[1, x)$:
$$\sum_{\substack{a \in A \\ 1 \leq a < x}} \frac{1}{a}.$$ -/
noncomputable def reciprocalSum (A : Set ℕ) (x : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Ico 1 x).filter (· ∈ A), (1 : ℝ) / (a : ℝ)

/-- Erdős Problem 444 [ErGr80, p.88] (PROVED):

Let $A \subseteq \mathbb{N}$ be infinite and $d_A(n)$ count the number of $a \in A$ dividing $n$.
For every $k$,
$$\limsup_{x \to \infty} \frac{\max_{n < x} d_A(n)}{\left(\sum_{a \in A \cap [1,x)}
\frac{1}{a}\right)^k} = \infty.$$

Equivalently, for every $M > 0$, there are arbitrarily large $x$ and some $n < x$
with $d_A(n) > M \cdot \left(\sum_{a \in A \cap [1,x)} \frac{1}{a}\right)^k$.

Proved by Erdős and Sárkőzy [ErSa80]. -/
@[category research solved, AMS 11]
theorem erdos_444 (A : Set ℕ) (hA : A.Infinite) (k : ℕ) :
    ∀ M : ℝ, 0 < M →
    ∃ᶠ x in atTop,
    ∃ n : ℕ, 1 ≤ n ∧ n < x ∧
    M * (reciprocalSum A x) ^ k < (divisorCountIn A n : ℝ) := by
  sorry

end Erdos444
