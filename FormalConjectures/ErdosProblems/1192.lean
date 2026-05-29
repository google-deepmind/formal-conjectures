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
# Erdős Problem 1192

*References:*
- [erdosproblems.com/1192](https://www.erdosproblems.com/1192)
- [Ru90] Ruzsa, Imre Z., A just basis. Monatsh. Math. (1990), 145--151.
-/

open Nat Filter Finset Set
open scoped Asymptotics Classical BigOperators

namespace Erdos1192

/--
For $A\subset \mathbb{N}$ let $f_r(n)$ count the number of solutions to $n=a_1+\cdots+a_r$
with $a_i\in A$.
-/
noncomputable def f_r (A : Set ℕ) (r n : ℕ) : ℕ :=
  { v : Fin r → ℕ | (∀ i, v i ∈ A) ∧ ∑ i, v i = n }.ncard

/--
Does there exist, for all $r\geq 2$, a basis $A$ of order $r$ (so that $f_r(n)>0$ for all
large $n$) such that $$\sum_{n\leq x}f_r(n)^2 \ll x$$ for all $x$?
-/
@[category research open, AMS 5]
theorem erdos_1192 :
    answer(sorry) ↔
      ∀ r ≥ 2, ∃ A : Set ℕ,
        (∀ᶠ n in atTop, f_r A r n > 0) ∧
        (fun (x : ℕ) ↦ ∑ n ∈ range (x + 1), (f_r A r n : ℝ) ^ 2) =O[atTop]
          (fun (x : ℕ) ↦ (x : ℝ)) := by
  sorry

/--
Erdős and Rényi proved by the probabilistic method that there exists a set $A$ such that
$$\sum_{n\leq x}f_r(n)^2 \ll x$$ and $$\lvert A\cap [1,x]\rvert\gg x^{1/r}$$ for all $x$.
-/
@[category research solved, AMS 5]
theorem erdos_1192.variants.renyi :
    ∀ r ≥ 2, ∃ A : Set ℕ,
      ((fun (x : ℕ) ↦ ∑ n ∈ range (x + 1), (f_r A r n : ℝ) ^ 2) =O[atTop]
        (fun (x : ℕ) ↦ (x : ℝ))) ∧
      ((fun (x : ℕ) ↦ (x : ℝ) ^ (1 / (r : ℝ))) =O[atTop]
        (fun (x : ℕ) ↦ (count A x : ℝ))) := by
  sorry

/--
Ruzsa [Ru90] proved that the answer is yes for $r=2$.
-/
@[category research solved, AMS 5]
theorem erdos_1192.variants.ruzsa :
    ∃ A : Set ℕ,
      (∀ᶠ n in atTop, f_r A 2 n > 0) ∧
      (fun (x : ℕ) ↦ ∑ n ∈ range (x + 1), (f_r A 2 n : ℝ) ^ 2) =O[atTop]
        (fun (x : ℕ) ↦ (x : ℝ)) := by
  sorry

end Erdos1192
