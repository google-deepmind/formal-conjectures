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
# Erdős Problem 873

*Reference:* [erdosproblems.com/873](https://www.erdosproblems.com/873)
-/
/--Let $a$ be some sequence of natural numbers. We set $F(A,X,k)$ to be the count of
the number of $i$ such that $[a_i,a_{i+1}, … ,a_{i+k−1}] < X$,
where the left-hand side is the least common multiple.-/
private noncomputable abbrev F (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (Finset.range k).lcm (fun m => a (i + m)) < X}.encard

/--Let $A = \{a_1 < a_2 <⋯\} ⊆ ℕ$ and let $F(A,X,k)$ count the number of $i$ such that
$[a_i,a_{i+1}, … ,a_{i+k−1}] < X$, where the left-hand side is the least common multiple.
Is it true that, for every $ϵ > 0$, there exists some $k$ such that $F(A,X,k) < X^ϵ$?-/
@[category research open, AMS 11]
theorem erdos_873 : (∀ᵉ (a : ℕ → ℕ) (ε > (0 : ℝ)), 0 < a 0 → StrictMono a →
    ∃ k, ∀ X > 0, F a X k < (X^ε).toEReal) ↔ answer(sorry) := by
  sorry
