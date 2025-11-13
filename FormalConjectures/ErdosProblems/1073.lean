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
# Erdős Problem 1073

*Reference:* [erdosproblems.com/1065](https://www.erdosproblems.com/1073)
-/

open Nat Filter Finset

namespace Erdos1073

/--
Let $A(x)$ count the number of composite $u < x$ such that $n!+1 \equiv 0 (\mod u)$ for some $n$.
-/
noncomputable def A (x : ℕ) : ℝ := {u | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x}.ncard

/-- Is it true that $A(x) ≤ x^{o(1)}$? -/
@[category research open, AMS 11]
theorem erdos_1073a : (A =o[atTop] (fun x ↦ (x : ℝ))) ↔ answer(sorry) := by
  sorry

/-- Is it true that $f(p)/p \to 0$ for almost all $p$? -/
@[category research open, AMS 11]
theorem erdos_1073b :
    (∃ (P : Finset ℕ), (∀ p ∈ P, p.Prime) ∧
      ∀ᵉ ε > (0 : ℝ), ∃ N₀, ∀ p ≥ N₀, p.Prime ∧ p ∉ P → f p / p < ε)
    ↔ answer(sorry) := by
  sorry

/--
Erdős, Hardy, and Subbarao [HaSu02], believed that the number of $p \le x$ for which $f(p)=p−1$
is $o(x/logx)$.

[HaSu02] Hardy, G. E. and Subbarao, M. V., _A modified problem of Pillai and some related questions._
Amer. Math. Monthly (2002), 554--559.
-/
@[category research open, AMS 11]
theorem erdos_1073a.variants.littleo :
    (fun x ↦ (#({p | p.Prime ∧ f p = p - 1} ∩ Finset.range (x + 1)).toFinset : ℝ)) =o[atTop]
      (fun x ↦ x / Real.log x) := by
  sorry

end Erdos1073
