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
# Büchi's problem

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/B%C3%BCchi%27s_problem)
-/

namespace Buchi

/-- `IsBuchi M` asserts that whenever `M` consecutive values `(x + n)² + a` (for
`n = 0, …, M - 1`) are all perfect squares, then `a` must be `0`. -/
def IsBuchi (M : ℕ) : Prop :=
  ∀ x a : ℤ, (∀ n ∈ Finset.range M, IsSquare ((x + (n : ℤ)) ^ 2 + a)) → a = 0

/--
**Büchi's problem**
There exists a positive integer $M$ such that, for all integers $x$ and $a$,
if $(x+n)^2 + a$ is a square for $M$ consecutive values of $n$, then $a = 0$.
-/
@[category research open, AMS 11]
theorem buchi_problem :
    answer(sorry) ↔ ∃ M : ℕ, 1 ≤ M ∧ IsBuchi M := by
  sorry


/--
**Büchi's problem (first open case, $M = 5$)**:
For all integers $x$ and $a$, if $(x+n)^2 + a$ is a perfect square for $n = 0, 1, 2, 3, 4$,
then $a = 0$.

Non-trivial sequences of length 3 and 4 are known to exist, so $M = 5$ is the first open case.
-/
@[category research open, AMS 11]
theorem buchi_problem_M5 : IsBuchi 5 := by
  sorry

/-- The case $M = 0$ fails: the hypothesis is vacuous, so $a = 0$ cannot be concluded. -/
@[category test, AMS 11]
theorem buchi_false_M0 : ¬ IsBuchi 0 := by
  simp only [IsBuchi, Finset.range_zero, not_forall, exists_prop]
  exact ⟨0, 1, by norm_num⟩

/-- The case $M = 1$ fails: $0^2 + 4 = 4 = 2^2$ is a square but $a = 4 \neq 0$. -/
@[category test, AMS 11]
theorem buchi_false_M1 : ¬ IsBuchi 1 := by
  simp only [IsBuchi, not_forall]
  refine ⟨0, 4, ?_, by norm_num⟩
  intro n hn
  simp only [Finset.range_one, Finset.mem_singleton] at hn; subst hn
  exact ⟨2, by norm_num⟩

/-- The case $M = 2$ fails: $(7+n)^2 - 48$ is a perfect square for $n = 0, 1$
($1^2$ and $4^2$), but $a = -48 \neq 0$. -/
@[category test, AMS 11]
theorem buchi_false_M2 : ¬ IsBuchi 2 := by
  simp only [IsBuchi, not_forall]
  refine ⟨7, -48, ?_, by norm_num⟩
  intro n hn
  simp [Finset.mem_range] at hn
  interval_cases n
  · exact ⟨1, by norm_num⟩
  · exact ⟨4, by norm_num⟩

/-- The case $M = 3$ fails: $(24+n)^2 - 576$ is a perfect square for $n = 0, 1, 2$
($0^2$, $7^2$, and $10^2$), but $a = -576 \neq 0$. -/
@[category test, AMS 11]
theorem buchi_false_M3 : ¬ IsBuchi 3 := by
  simp only [IsBuchi, not_forall]
  refine ⟨24, -576, ?_, by norm_num⟩
  intro n hn
  simp [Finset.mem_range] at hn
  interval_cases n
  · exact ⟨0, by norm_num⟩
  · exact ⟨7, by norm_num⟩
  · exact ⟨10, by norm_num⟩

/-- The case $M = 4$ fails: $(246+n)^2 - 60480$ is a perfect square for $n = 0, 1, 2, 3$
($6^2$, $23^2$, $32^2$, and $39^2$), but $a = -60480 \neq 0$.
The sequence $(6, 23, 32, 39)$ is a nontrivial Büchi sequence of length 4 (Hensley 1983). -/
@[category test, AMS 11]
theorem buchi_false_M4 : ¬ IsBuchi 4 := by
  simp only [IsBuchi, not_forall]
  refine ⟨246, -60480, ?_, by norm_num⟩
  intro n hn
  simp [Finset.mem_range] at hn
  interval_cases n
  · exact ⟨6, by norm_num⟩
  · exact ⟨23, by norm_num⟩
  · exact ⟨32, by norm_num⟩
  · exact ⟨39, by norm_num⟩

end Buchi
