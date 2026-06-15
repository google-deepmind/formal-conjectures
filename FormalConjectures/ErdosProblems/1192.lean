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
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory.
  Ann. Discrete Math. 6 (1980), 89--115.
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

/-- The empty sum ($r = 0$) gives exactly one representation of $0$: the empty tuple. -/
@[category test, AMS 5 11]
theorem erdos_1192.f_r_zero_zero (A : Set ℕ) : f_r A 0 0 = 1 := by
  dsimp [f_r]
  have h : { v : Fin 0 → ℕ | (∀ i, v i ∈ A) ∧ ∑ i, v i = 0 } = { default } := by
    ext v
    simp [eq_iff_true_of_subsingleton]
  rw [h, Set.ncard_singleton]

/-- With an empty set, there are no valid $r$-tuples for $r \geq 1$. -/
@[category test, AMS 5 11]
theorem erdos_1192.f_r_empty (r n : ℕ) : f_r ∅ (r + 1) n = 0 := by
  dsimp [f_r]
  have h : { v : Fin (r + 1) → ℕ | (∀ i, v i ∈ (∅ : Set ℕ)) ∧ ∑ i, v i = n } = ∅ := by
    ext v
    simp
  rw [h, Set.ncard_empty]

/-- For $r = 1$, $f_1(\{n\}, n) = 1$: the only $1$-tuple from $\{n\}$ summing to $n$ is $(n)$. -/
@[category test, AMS 5 11]
theorem erdos_1192.f_r_singleton_self (n : ℕ) : f_r {n} 1 n = 1 := by
  dsimp [f_r]
  have h : { v : Fin 1 → ℕ | (∀ i, v i ∈ ({n} : Set ℕ)) ∧ ∑ i, v i = n } = { fun _ ↦ n } := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, _⟩
      ext i
      exact h1 i
    · rintro rfl
      refine ⟨fun _ ↦ rfl, ?_⟩
      simp
  rw [h, Set.ncard_singleton]

/-- $f_1(\{0\}, 1) = 0$: can't represent $1$ with a single element from $\{0\}$. -/
@[category test, AMS 5 11]
theorem erdos_1192.f_r_no_rep : f_r {0} 1 1 = 0 := by
  dsimp [f_r]
  have h : { v : Fin 1 → ℕ | (∀ i, v i ∈ ({0} : Set ℕ)) ∧ ∑ i, v i = 1 } = ∅ := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    have h3 : v = fun _ ↦ 0 := by ext i; exact h1 i
    rw [h3] at h2
    revert h2
    simp
  rw [h, Set.ncard_empty]

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
