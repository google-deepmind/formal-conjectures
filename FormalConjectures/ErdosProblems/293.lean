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
# Erdős Problem 293

*Reference:* [erdosproblems.com/293](https://www.erdosproblems.com/293)

Let $k \geq 1$ and let $v(k)$ be the minimal integer which does not appear as some $n_i$
in a solution to $1 = 1/n_1 + \cdots + 1/n_k$ with $1 \leq n_1 < \cdots < n_k$.
Estimate the growth of $v(k)$.

Known bounds:
- $v(k) \gg k!$ (Bleicher–Erdős [BlEr75])
- $v(k) \geq e^{ck^2}$ for some $c > 0$ (van Doorn–Tang [vDTa25b])
- $v(k) \leq k \cdot c_0^{2^k}$ where $c_0 \approx 1.26408$ is the Vardi constant

It may be that $v(k)$ grows doubly exponentially in $\sqrt{k}$ or even $k$.

[BlEr75] Bleicher, M.N. and Erdős, P., *Denominators of Egyptian fractions*, J. Number Theory (1975).

[vDTa25b] van Doorn, F. and Tang, R. (2025).

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*, Monographies de L'Enseignement Mathématique (1980).
-/

open BigOperators Real Filter Finset Classical

namespace Erdos293

/-- A positive integer $n$ appears in a $k$-term Egyptian fraction representation of $1$
if there exists a $k$-element set $S$ of distinct positive integers with $n \in S$
such that $\sum_{m \in S} 1/m = 1$. -/
def AppearsInKTermEgyptian (k n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.card = k ∧ n ∈ S ∧ (∀ m ∈ S, 0 < m) ∧
    ∑ m ∈ S, (1 : ℚ) / (m : ℚ) = 1

/-- $v(k)$ is the smallest positive integer that does not appear in any representation
of $1$ as a sum of exactly $k$ distinct unit fractions. -/
noncomputable def v (k : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ¬AppearsInKTermEgyptian k n}

/-- Bleicher–Erdős lower bound [BlEr75]:
There exists a constant $c > 0$ such that $v(k) \geq c \cdot k!$ for all $k \geq 1$. -/
@[category research solved, AMS 11]
theorem erdos_293.variants.bleicher_erdos_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      c * (Nat.factorial k : ℝ) ≤ (v k : ℝ) := by
  sorry

/-- van Doorn–Tang lower bound [vDTa25b]:
There exists a constant $c > 0$ such that $v(k) \geq e^{ck^2}$ for all
sufficiently large $k$. -/
@[category research solved, AMS 11]
theorem erdos_293.variants.van_doorn_tang_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      exp (c * (k : ℝ) ^ 2) ≤ (v k : ℝ) := by
  sorry

/-- Upper bound: $v(k) \leq k \cdot c_0^{2^k}$ where $c_0$ is the Vardi constant
($\approx 1.26408$).
There exists $c_0 > 1$ such that $v(k) \leq k \cdot c_0^{2^k}$ for all $k \geq 1$. -/
@[category research solved, AMS 11]
theorem erdos_293.variants.upper_bound :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ k : ℕ, 1 ≤ k →
      (v k : ℝ) ≤ (k : ℝ) * c₀ ^ ((2 : ℝ) ^ (k : ℕ)) := by
  sorry

/--
Erdős Problem 293 [ErGr80, p.35]:

Conjecture: $v(k)$ grows doubly exponentially in $k$. That is, there exists a
constant $c > 0$ such that $v(k) \geq e^{e^{ck}}$ for all sufficiently large $k$.

(A weaker form conjectures doubly exponential growth in $\sqrt{k}$.)
-/
@[category research open, AMS 11]
theorem erdos_293 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      exp (exp (c * (k : ℝ))) ≤ (v k : ℝ) := by
  sorry

end Erdos293
