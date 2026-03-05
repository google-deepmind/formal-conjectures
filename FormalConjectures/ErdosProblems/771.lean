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
# Erdős Problem 771

*Reference:* [erdosproblems.com/771](https://www.erdosproblems.com/771)

Let $f(n)$ be maximal such that, for every $m \geq 1$, there exists some
$S \subseteq \{1, \ldots, n\}$ with $|S| = f(n)$ such that $m \neq \sum_{a \in A} a$
for all $A \subseteq S$.

Is it true that $f(n) = (\tfrac{1}{2} + o(1)) \cdot n / \log n$?

The lower bound $f(n) \geq (\tfrac{1}{2} + o(1)) \cdot n / \log n$ was proved by Erdős
and Graham, who took $S = \{kp : 1 \leq k < n/p\}$ where $p$ is the least prime not
dividing $m$. The matching upper bound was proved by Alon and Freiman [AlFr88].

[AlFr88] Alon, N. and Freiman, G., _On sums of subsets of a set of integers_. Combinatorica
8 (1988), 297-306.
-/

open Finset Real

namespace Erdos771

/-- $m$ is a subset sum of $S$: there exists $A \subseteq S$ with $\sum_{a \in A} a = m$. -/
def IsSubsetSum (S : Finset ℕ) (m : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ S ∧ A.sum id = m

/-- $f(n)$ is the maximum $k$ such that for every positive integer $m$, there exists
a $k$-element subset $S \subseteq \{1, \ldots, n\}$ for which $m$ is not a subset sum
of $S$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ m : ℕ, m ≥ 1 →
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ S.card = k ∧ ¬IsSubsetSum S m}

/--
Erdős Problem 771 (Erdős–Graham + Alon–Freiman [AlFr88]):
$f(n) = (\tfrac{1}{2} + o(1)) \cdot n / \log n$.

Formally: for every $\varepsilon > 0$, there exists $N_0$ such that for all $n \geq N_0$,
$$(\tfrac{1}{2} - \varepsilon) \cdot n / \log n \leq f(n) \leq (\tfrac{1}{2} + \varepsilon) \cdot n / \log n.$$
-/
@[category research solved, AMS 11]
theorem erdos_771 : answer(True) ↔
    (∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (1 / 2 - ε) * (↑n / Real.log ↑n) ≤ ↑(f n) ∧
      ↑(f n) ≤ (1 / 2 + ε) * (↑n / Real.log ↑n)) := by
  sorry

end Erdos771
