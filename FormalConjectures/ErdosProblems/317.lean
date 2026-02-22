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
open Finset
open Filter

/--
Is there some constant $c>0$ such that for every $n\geq 1$ there exists some $\delta_k\in \{-1,0,1\}$ for $1\leq k\leq n$ with
\[0< \left\lvert \sum_{1\leq k\leq n}\frac{\delta_k}{k}\right\rvert < \frac{c}{2^n}?\]
-/
@[category research open, AMS 11]
theorem erdos_317 : answer(sorry) ↔
    ∃ c > 0, ∀ n ≥ 1, ∃ δ : Fin n → ℚ,
      Set.range δ ⊆ {-1, 0, 1} ∧
      letI lhs : ℝ := |∑ k, (δ k) / (k + 1)|
      0 < lhs ∧ lhs < c / 2^n := by
  sorry

/--
Is it true that for sufficiently large $n$, for any $\delta_k\in \{-1,0,1\}$,
\[\left\lvert \sum_{1\leq k\leq n}\frac{\delta_k}{k}\right\rvert > \frac{1}{[1,\ldots,n]}\]
whenever the left-hand side is not zero?
-/
@[category research open, AMS 11]
theorem erdos_317.variants.claim2 : answer(sorry) ↔
    ∀ᶠ n in atTop, ∀ δ : (Fin n) → ℚ, δ '' Set.univ ⊆ {-1,0,1} →
    letI lhs := |∑ k, ((δ k : ℚ) / (k + 1))|
    lhs ≠ 0 → lhs > 1 / (Icc 1 n).lcm id := by
  sorry

/--
Inequality in `erdos_317.variants.claim2` is obvious, the problem is strict inequality.
-/
@[category undergraduate, AMS 11]
lemma claim2_inequality : ∀ᶠ n in atTop,
    ∀ δ : (Fin n) → ℚ, δ '' Set.univ ⊆ {-1,0,1} →
    letI lhs := |∑ k, ((δ k : ℚ) / (k + 1))|
    lhs ≠ 0 → lhs ≥ 1 / (Icc 1 n).lcm id := by
  sorry

/--
`erdos_317.variants.claim2` fails for small $n$, for example
\[\frac{1}{2}-\frac{1}{3}-\frac{1}{4}=-\frac{1}{12}.\]
-/
@[category graduate, AMS 11]
theorem erdos_317.variants.counterexample : ¬ (∀  δ : (Fin 4) → ℚ, δ '' Set.univ ⊆ {-1,0,1} →
    letI lhs := |∑ k, ((δ k : ℚ) / (k + 1))|
    lhs ≠ 0 → lhs > (1 : ℚ) / ((Icc 1 4).lcm id : ℕ)) := by
  push_neg
  use ![0, 1, -1, -1]
  norm_num [Finset.sum]
  exact ⟨by grind, by simp; rfl⟩

end Erdos317
