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
# Erdős Problem 323

*Reference:* [erdosproblems.com/323](https://www.erdosproblems.com/323)
-/

open Filter
open scoped Asymptotics

namespace Erdos323

/--
Let $1\leq m\leq k$ and $f_{k,m}(x)$ denote the number of integers $\leq x$ which are the sum of
$m$ many nonnegative $k$th powers.
-/
noncomputable def f (k m x : ℕ) : ℕ :=
  { n : ℕ | n ≤ x ∧ ∃ (v : Fin m → ℕ), n = ∑ i, v i ^ k }.ncard

/--
Is it true that $f_{k,k}(x) \gg_\epsilon x^{1-\epsilon}$ for all $\epsilon>0$?

This would have significant applications to Waring's problem. Erdős and Graham describe this as
'unattackable by the methods at our disposal'.
-/
@[category research open, AMS 11]
theorem erdos_323.parts.i :
    answer(sorry) ↔ ∀ k ≥ 1, ∀ ε > (0 : ℝ),
      (fun (x : ℕ) ↦ (x : ℝ) ^ (1 - ε)) =O[atTop] (fun (x : ℕ) ↦ (f k k x : ℝ)) := by
  sorry

/--
Is it true that if $m < k$ then $f_{k,m}(x) \gg x^{m/k}$ for sufficiently large $x$?
-/
@[category research open, AMS 11]
theorem erdos_323.parts.ii :
    answer(sorry) ↔ ∀ k m : ℕ, 1 ≤ m → m < k →
      (fun (x : ℕ) ↦ (x : ℝ) ^ ((m : ℝ) / (k : ℝ))) =O[atTop] (fun (x : ℕ) ↦ (f k m x : ℝ)) := by
  sorry

/--
The case $k=2$ was resolved by Landau, who showed $f_{2,2}(x) \sim \frac{cx}{\sqrt{\log x}}$ for
some constant $c>0$.
-/
@[category research solved, AMS 11]
theorem erdos_323.variants.k_eq_2 :
    ∃ c > 0, (fun (x : ℕ) ↦ (f 2 2 x : ℝ)) ~[atTop]
      (fun (x : ℕ) ↦ c * (x : ℝ) / Real.sqrt (Real.log (x : ℝ))) := by
  sorry

/--
For $k>2$ it is not known if $f_{k,k}(x)=o(x)$.
-/
@[category research open, AMS 11]
theorem erdos_323.variants.k_gt_2 :
    answer(sorry) ↔ ∀ k > 2, (fun (x : ℕ) ↦ (f k k x : ℝ)) =o[atTop] (fun (x : ℕ) ↦ (x : ℝ)) := by
  sorry

end Erdos323
