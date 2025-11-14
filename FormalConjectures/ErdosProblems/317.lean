/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 317

*Reference:* [erdosproblems.com/317](https://www.erdosproblems.com/317)
-/

namespace Erdos317

/--
The least common multiple of the numbers 1,...,n.
-/
abbrev lcm_one_to_n : ℕ → ℕ
    | 0 => 1
    | n + 1 => (lcm_one_to_n n).lcm (n + 1)

/--
Inequality is obvious for `erdos_317.variants.claim2`, the problem is strict inequality.
This fails for small $n$, for example\[\frac{1}{2}-\frac{1}{3}-\frac{1}{4}=-\frac{1}{12}.\]
-/
@[category API, AMS 11]
lemma claim2_inequality : ∃ N : ℕ, ∀ n ≥ N,
    ∀ δ : ℕ → ℝ, δ '' (Finset.Icc 1 n) ⊆ {-1,0,1} →
    abs (∑ k ∈ Finset.Icc 1 n, ((δ k : ℝ) / k)) ≠ 0 →
        abs (∑ k ∈ Finset.Icc 1 n, ((δ k : ℝ) / k)) ≥ 1 / (lcm_one_to_n n : ℝ) := by
  sorry

/--
Is there some constant $c>0$ such that for every $n\geq 1$ there exists some $\delta_k\in \{-1,0,1\}$ for $1\leq k\leq n$ with
\[0< \left\lvert \sum_{1\leq k\leq n}\frac{\delta_k}{k}\right\rvert < \frac{c}{2^n}?\]
-/
@[category research open, AMS 11]
theorem erdos_317 : (∃ c : ℝ, c > 0 → ∀ n ≥ 1,
    ∃ δ : ℕ → ℝ, δ '' (Finset.Icc 1 n) ⊆ {-1,0,1} ∧
              0 < abs (∑ k ∈ Finset.Icc 1 n, ((δ k : ℝ) / k)) ∧
        c / 2^n > abs (∑ k ∈ Finset.Icc 1 n, ((δ k : ℝ) / k))) ↔ answer(sorry) := by
  sorry

/--
Is it true that for sufficiently large $n$, for any $\delta_k\in \{-1,0,1\}$,
\[\left\lvert \sum_{1\leq k\leq n}\frac{\delta_k}{k}\right\rvert > \frac{1}{[1,\ldots,n]}\]
whenever the left-hand side is not zero?
-/
@[category research open, AMS 11]
theorem erdos_317.variants.claim2 : (∃ N : ℕ, ∀ n ≥ N,
    ∀ δ : ℕ → ℝ, δ '' (Finset.Icc 1 n) ⊆ {-1,0,1} →
    abs (∑ k ∈ Finset.Icc 1 n, ((δ k : ℝ) / k)) ≠ 0 →
        abs (∑ k ∈ Finset.Icc 1 n, ((δ k : ℝ) / k)) > 1 / (lcm_one_to_n n : ℝ)) ↔ answer(sorry) := by
  sorry

end Erdos317
