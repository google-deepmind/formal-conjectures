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
# Erdős Problem 796

Let $g_k(n)$ denote the largest size of a subset $A \subseteq \{1, \ldots, n\}$ such that every
integer has fewer than $k$ representations as a product $a_1 \cdot a_2$ with $a_1 < a_2$ and
$a_1, a_2 \in A$. Is it true that
$g_3(n) = \frac{n \log \log n}{\log n} + (c + o(1)) \frac{n}{\log n}$ for some constant $c$?

*Reference:* [erdosproblems.com/796](https://www.erdosproblems.com/796)

[Er69] Erdős, P., _On some applications of graph theory to number theoretic problems_. Publ.
Ramanujan Inst. 1 (1969), 131-136.
-/

open Finset

namespace Erdos796

/-- The number of representations of $m$ as $a_1 \cdot a_2$ with $a_1 < a_2$ and
$a_1, a_2 \in A$. For each $a_1 \in A$, we check whether $m / a_1 \in A$,
$a_1 < m / a_1$, and $a_1$ divides $m$ (verified by $a_1 \cdot (m / a_1) = m$). -/
def productRepCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a₁ => m / a₁ ∈ A ∧ a₁ < m / a₁ ∧ a₁ * (m / a₁) = m)).card

/-- $g_k(n)$: the largest cardinality of $A \subseteq \{1, \ldots, n\}$ such that every $m$ has
fewer than $k$ representations as $a_1 \cdot a_2$ with $a_1 < a_2$, $a_1, a_2 \in A$. -/
noncomputable def multiplicativeBkMax (k n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧
    (∀ m, productRepCount A m < k) ∧ A.card = s}

/--
Erdős Problem 796 [Er69, p.80]:

There exists a constant $c$ such that
$$g_3(n) = \frac{n \log \log n}{\log n} + (c + o(1)) \cdot \frac{n}{\log n}.$$

Formulated as: there exists $c$ such that for every $\varepsilon > 0$, there exists $N_0$
such that for all $n \ge N_0$,
$$\left| g_3(n) - \frac{n \log \log n}{\log n} - \frac{cn}{\log n} \right|
  \le \frac{\varepsilon \, n}{\log n}.$$
-/
@[category research open, AMS 5 11]
theorem erdos_796 :
    answer(sorry) ↔
    ∃ c : ℝ, ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      |(multiplicativeBkMax 3 n : ℝ) -
        (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) -
        c * (n : ℝ) / Real.log (n : ℝ)| ≤
      ε * (n : ℝ) / Real.log (n : ℝ) := by
  sorry

end Erdos796
