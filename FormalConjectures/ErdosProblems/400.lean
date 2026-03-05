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
# Erdős Problem 400

*Reference:* [erdosproblems.com/400](https://www.erdosproblems.com/400)

For any $k \geq 2$, let $g_k(n)$ denote the maximum value of $(a_1 + \cdots + a_k) - n$ where
$a_1, \ldots, a_k$ are natural numbers such that $a_1! \cdots a_k! \mid n!$.

Erdős and Graham note that $g_k(n) \ll_k \log n$ always, but the best possible constant is unknown.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter

open scoped BigOperators

namespace Erdos400

/-- $g_k(n)$ is the maximum of $(a_1 + \cdots + a_k) - n$ over all $k$-tuples of natural numbers
$(a_1, \ldots, a_k)$ satisfying $a_1! \cdots a_k! \mid n!$. -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ a : Fin k → ℕ, (∏ i, (a i).factorial) ∣ n.factorial ∧
    s = (∑ i, a i) - n}

/--
Erdős Problem 400, Part 1 [ErGr80, p.77]:

For any $k \geq 2$, there exists a constant $c_k > 0$ such that
$$\sum_{n \leq x} g_k(n) \sim c_k \cdot x \cdot \log x.$$

Formalized as: the ratio $\left(\sum_{n=1}^{x} g_k(n)\right) / (x \cdot \log x)$ tends to $c_k$
as $x \to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_400 (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun x : ℕ =>
        (∑ n ∈ Finset.Icc 1 x, (g k n : ℝ)) / ((x : ℝ) * Real.log (x : ℝ)))
        atTop (nhds c) := by
  sorry

/--
Erdős Problem 400, Part 2 [ErGr80, p.77]:

For any $k \geq 2$, there exists a constant $c_k$ such that for almost all $n \leq x$,
$g_k(n) = c_k \cdot \log x + o(\log x)$.

Formalized as: for every $\varepsilon > 0$, the proportion of $n \leq x$ for which
$|g_k(n) - c_k \cdot \log x| > \varepsilon \cdot \log x$ tends to $0$ as $x \to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_400.variants.concentration (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun x : ℕ =>
        (((Finset.Icc 1 x).filter (fun n =>
          |(g k n : ℝ) - c * Real.log (x : ℝ)| >
            ε * Real.log (x : ℝ))).card : ℝ) / (x : ℝ))
        atTop (nhds 0) := by
  sorry

end Erdos400
