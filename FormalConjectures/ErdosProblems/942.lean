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
# Erdős Problem 942

*Reference:* [erdosproblems.com/942](https://www.erdosproblems.com/942)
-/

open Nat Filter Topology

/--
Let $h(n)$ count the number of powerful integers in $[n^2, (n + 1)^2)$.
-/
def erdos_942.h (n : ℕ) : ℕ := ((Finset.Ico (n ^ 2) ((n + 1) ^ 2)).filter Powerful).card

/--
Is there some constant $c > 0$ such that $h(n) < (\log n)^{c + o(1)}$ and, for infinitely many $n$,
$h(n) > (\log n)^{c - o(1)}$.
-/
@[category research open, AMS 11]
theorem erdos_942 : (∃ c > 0, ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ n, erdos_942.h n < (Real.log n) ^ (c + o n) ∧
    {n | erdos_942.h n > (Real.log n) ^ (c - o n)}.Infinite) := by
  sorry

/--
It is not hard to prove that $\limsup h(n) = \infty$.
-/
@[category graduate, AMS 11]
theorem erdos_942.variants.limsup :
    atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h)) = ⊤ := by
  sorry


/--
It is not hard to prove that the density $δ_l$ of integers for which $h(n) = l$ exists
-/
@[category graduate, AMS 11]
theorem erdos_942.variants.density :
    ∃ δ : ℕ → ℝ, ∀ l, {n | erdos_942.h n = l}.HasDensity (δ l) ∧
    ∑' l, δ l = 1 := by
  sorry
