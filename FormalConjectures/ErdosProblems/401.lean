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
# Erdős Problem 401

*Reference:* [erdosproblems.com/401](https://www.erdosproblems.com/401)

Is there a function $f(r) \to \infty$ such that for infinitely many $n$ there exist $a_1, a_2$
with $a_1! \cdot a_2! \mid n! \cdot p_1^n \cdots p_r^n$ and
$a_1 + a_2 > n + f(r) \log n$, where $p_1, \ldots, p_r$ are the first $r$ primes?

Solved in the affirmative by Barreto and Leeham, using essentially the same construction as
their solution to Problem 729. Sothanaphan disproved the "for all large $n$" variant.

Related problems: #400, #728, #729. Problem 401 is arguably a more precisely stated form of
Problem 729.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter

open scoped BigOperators

namespace Erdos401

/--
Erdős Problem 401 [ErGr80, p.78]:

Is there a function $f : \mathbb{N} \to \mathbb{R}$ with $f(r) \to \infty$ as $r \to \infty$,
such that for every $r$, there are infinitely many $n$ for which there exist $a_1, a_2 \in \mathbb{N}$
with $a_1! \cdot a_2! \mid n! \cdot p_1^n \cdot p_2^n \cdots p_r^n$ and
$a_1 + a_2 > n + f(r) \cdot \log n$?
-/
@[category research solved, AMS 11]
theorem erdos_401 :
    answer(True) ↔
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ r : ℕ, {n : ℕ | ∃ a₁ a₂ : ℕ,
        (a₁.factorial * a₂.factorial) ∣
          (n.factorial * ∏ i ∈ Finset.range r, (Nat.nth Nat.Prime i) ^ n) ∧
        ((a₁ + a₂ : ℕ) : ℝ) > (n : ℝ) + f r * Real.log (n : ℝ)}.Infinite := by
  sorry

/--
Variant of Erdős Problem 401 with "for all sufficiently large $n$" in place of "for infinitely
many $n$". Disproved by Sothanaphan, who showed that when $n = p_{r+1}^k - 1$ the divisibility
condition constrains $a_1 + a_2 \leq n + O(\log n)$ with a bounded constant.
-/
@[category research solved, AMS 11]
theorem erdos_401_forall_large :
    answer(False) ↔
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ r : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∃ a₁ a₂ : ℕ,
        (a₁.factorial * a₂.factorial) ∣
          (n.factorial * ∏ i ∈ Finset.range r, (Nat.nth Nat.Prime i) ^ n) ∧
        ((a₁ + a₂ : ℕ) : ℝ) > (n : ℝ) + f r * Real.log (n : ℝ) := by
  sorry

end Erdos401
