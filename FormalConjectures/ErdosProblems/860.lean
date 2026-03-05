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
# Erdős Problem 860

*Reference:* [erdosproblems.com/860](https://www.erdosproblems.com/860)

Let $h(n)$ be such that, for any $m \geq 1$, in the interval $(m, m + h(n))$ there
exist distinct integers $a_i$ for $1 \leq i \leq \pi(n)$ such that $p_i \mid a_i$, where $p_i$
denotes the $i$-th prime.

Estimate $h(n)$.

A problem of Erdős and Pomerance [ErPo80], who proved that
$h(n) \ll n^{3/2} / (\log n)^{1/2}$.
Erdős and Selfridge proved $h(n) > (3 - o(1))n$, and Ruzsa proved $h(n)/n \to \infty$.

[ErPo80] Erdős, P. and Pomerance, C., *Matching the natural numbers up to n with distinct
multiples in another interval*, Nederl. Akad. Wetensch. Indag. Math. (1980).
-/

open Filter

namespace Erdos860

/-- A prime covering of $(m, m + h)$ for primes up to $n$: an injective assignment
of distinct integers in $(m, m + h)$, one for each prime $p \leq n$, such that
$p$ divides the integer assigned to it. -/
def HasPrimeCovering (n m h : ℕ) : Prop :=
  ∃ a : {p : ℕ // p.Prime ∧ p ≤ n} → ℕ,
    Function.Injective a ∧
    (∀ p, m < a p ∧ a p < m + h) ∧
    (∀ p, p.val ∣ a p)

/-- `erdosPomeranceH n` is the smallest $h$ such that for every $m \geq 1$,
in the open interval $(m, m + h)$ one can find $\pi(n)$ distinct multiples,
one for each prime $p \leq n$. -/
noncomputable def erdosPomeranceH (n : ℕ) : ℕ :=
  sInf {h : ℕ | ∀ m : ℕ, m ≥ 1 → HasPrimeCovering n m h}

/--
Erdős Problem 860, upper bound (Erdős–Pomerance [ErPo80]):

There exists $C > 0$ such that for all sufficiently large $n$,
$$h(n) \leq C \cdot n^{3/2} / (\log n)^{1/2}.$$
-/
@[category research solved, AMS 11]
theorem erdos_860 :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdosPomeranceH n : ℝ) ≤
        C * (n : ℝ) ^ ((3 : ℝ) / 2) / (Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) := by
  sorry

/--
Erdős Problem 860, lower bound (Ruzsa):
$h(n) / n \to \infty$ as $n \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_860.variants.lower_ruzsa :
    Tendsto (fun n => (erdosPomeranceH n : ℝ) / (n : ℝ)) atTop atTop := by
  sorry

end Erdos860
