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
# Erdős Problem 1054

*Reference:* [erdosproblems.com/1054](https://www.erdosproblems.com/1054)
-/

namespace Erdos1054

open Classical Filter Asymptotics

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest
divisors of $m$ for some $k\geq 1$.-/
noncomputable def f (n : ℕ) : ℕ :=
  if h : ∃ᵉ (m) (k ≥ 1), n = ∑ i < k, Nat.nth (· ∈ m.divisors) i then
    Nat.find h
  else 0

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Is it true that $f(n)=o(n)$?-/
@[category research open, AMS 11]
theorem erdos_1054.parts.i : (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) ↔ answer(sorry) := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Is it true that $f(n)=o(n)$ for almost all $n$? -/
@[category research open, AMS 11]
theorem erdos_1054.parts.ii : ∃ (A : Set ℕ), A.HasDensity 1 ∧
    (fun (n : A) ↦ (f ↑n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Is it true that $\limsup f(n)/n=\infty$? -/
@[category research open, AMS 11]
theorem erdos_1054.parts.iii : ∃ (A : Set ℕ), A.HasDensity 1 ∧
    (fun (n : A) ↦ (f ↑n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Show that $f$ is undefined at $n=2$, i.e. we get the junk value $0$. -/
@[category high_school, AMS 11]
theorem f_undefined_at_2 : f 2 = 0 := by
  sorry

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest divisors
of $m$ for some $k\geq 1$. Show that $f$ is undefined at $n=5$, i.e. we get the junk value $0$. -/
@[category high_school, AMS 11]
theorem f_undefined_at_3 : f 5 = 0 := by
  sorry

end Erdos1054
