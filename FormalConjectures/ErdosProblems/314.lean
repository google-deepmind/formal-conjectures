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
# Erdős Problem 314

*Reference:* [erdosproblems.com/314](https://www.erdosproblems.com/314)

Let $n \geq 1$ and let $m$ be minimal such that $\sum_{k=n}^{m} \frac{1}{k} \geq 1$. Define
$\varepsilon(n) = \sum_{k=n}^{m} \frac{1}{k} - 1$. Is it true that
$\liminf_{n \to \infty} n^2 \varepsilon(n) = 0$?

This is true, proved by Lim and Steinerberger [LiSt24]. They further showed
that for any $\delta > 0$, there exist infinitely many $n$ such that
$n^2 \left|\sum_{k=n}^{m} \frac{1}{k} - 1\right| \ll \frac{1}{(\log n)^{5/4 - \delta}}$.

Erdős and Graham [ErGr80] believe the exponent $2$ is best possible, i.e.,
$\liminf \varepsilon(n) n^{2+\delta} = \infty$ for all $\delta > 0$.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[LiSt24] Lim, T. and Steinerberger, S., _On a problem of Erdős and Graham_ (2024).
-/

open Finset BigOperators Filter Classical

namespace Erdos314

/-- For any $n \geq 1$, there exists $m$ such that $\sum_{k=n}^{m} \frac{1}{k} \geq 1$.
This follows from the divergence of the harmonic series. -/
@[category undergraduate, AMS 40]
lemma exists_harmonic_partial_sum_ge_one (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 1 ≤ ∑ k ∈ Finset.Icc n m, (1 : ℝ) / (k : ℝ) := by sorry

/-- $m(n)$ is the minimal $m$ such that $\sum_{k=n}^{m} \frac{1}{k} \geq 1$, for $n \geq 1$.
Returns $0$ for $n = 0$. -/
noncomputable def erdos314M (n : ℕ) : ℕ :=
  if h : 1 ≤ n then
    Nat.find (exists_harmonic_partial_sum_ge_one n h)
  else 0

/-- $\varepsilon(n) = \sum_{k=n}^{m(n)} \frac{1}{k} - 1$, where $m(n)$ is minimal with
$\sum_{k=n}^{m(n)} \frac{1}{k} \geq 1$. -/
noncomputable def erdos314Epsilon (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc n (erdos314M n), (1 : ℝ) / (k : ℝ)) - 1

/--
Erdős Problem 314 [ErGr80] (proved by Lim–Steinerberger [LiSt24]):

Let $n \geq 1$ and let $m(n)$ be minimal such that $\sum_{k=n}^{m(n)} \frac{1}{k} \geq 1$.
Define $\varepsilon(n) = \sum_{k=n}^{m(n)} \frac{1}{k} - 1$. Then
$\liminf_{n \to \infty} n^2 \varepsilon(n) = 0$.

Equivalently: for every $\delta > 0$ and every $N_0$, there exists $n \geq N_0$ with
$n \geq 1$ such that $n^2 \varepsilon(n) < \delta$.
-/
@[category research solved, AMS 11 40]
theorem erdos_314 : answer(True) ↔
    (∀ δ : ℝ, 0 < δ → ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ 1 ≤ n ∧
      (n : ℝ) ^ 2 * erdos314Epsilon n < δ) := by
  sorry

end Erdos314
