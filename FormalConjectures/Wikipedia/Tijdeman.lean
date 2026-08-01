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

import FormalConjecturesUtil

/-!
# Tijdeman's theorem

Tijdeman's theorem (1976) asserts that the Catalan equation
$$y^m - x^n = 1$$
has only finitely many solutions in natural numbers $x, y > 1$ and $m, n > 1$.

This is strictly weaker than Catalan's conjecture / Mihăilescu's theorem (uniqueness of the
solution $3^2 - 2^3 = 1$), already formalised as `Catalan.catalans_conjecture` in
`FormalConjectures/Wikipedia/Catalan.lean`. The present file records the classical
*finiteness* theorem obtained via linear forms in logarithms.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Tijdeman%27s_theorem)
- R. Tijdeman, *On the equation of Catalan*, Acta Arith. 29 (1976), 197–209
-/

namespace Tijdeman

/--
Predicate: $(x, y, m, n)$ solves the Catalan equation $y^m = x^n + 1$ with bases and exponents
strictly greater than $1$. Written as an additive equation to avoid truncated subtraction on
$\mathbb{N}$.
-/
def IsCatalanSolution (x y m n : ℕ) : Prop :=
  1 < x ∧ 1 < y ∧ 1 < m ∧ 1 < n ∧ y ^ m = x ^ n + 1

/-- The set of Catalan solutions in $\mathbb{N}^4$ with bases and exponents $> 1$. -/
def CatalanEquationSolutions : Set (ℕ × ℕ × ℕ × ℕ) :=
  {p | IsCatalanSolution p.1 p.2.1 p.2.2.1 p.2.2.2}

/--
**Tijdeman's theorem.** The Catalan equation $y^m - x^n = 1$ has only finitely many solutions
in natural numbers $x, y > 1$ and $m, n > 1$.
-/
@[category research solved, AMS 11]
theorem tijdeman_theorem : CatalanEquationSolutions.Finite := by
  sorry

/-- Unpacked form of Tijdeman's theorem without the auxiliary solution set. -/
@[category API, AMS 11]
theorem tijdeman_theorem.unpacked :
    {(x, y, m, n) : ℕ × ℕ × ℕ × ℕ | IsCatalanSolution x y m n}.Finite := by
  simpa [CatalanEquationSolutions, IsCatalanSolution] using tijdeman_theorem

/--
Membership in the solution set is definitionally `IsCatalanSolution` on the four coordinates.
-/
@[category API, AMS 11]
theorem mem_catalanEquationSolutions_iff {x y m n : ℕ} :
    (x, y, m, n) ∈ CatalanEquationSolutions ↔ IsCatalanSolution x y m n := by
  simp [CatalanEquationSolutions, IsCatalanSolution]

/-- The classical solution $3^2 = 2^3 + 1$ (i.e. $3^2 - 2^3 = 1$). -/
@[category test, AMS 11]
theorem isCatalanSolution_classic : IsCatalanSolution 2 3 2 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

@[category test, AMS 11]
theorem solution_classic_mem : (2, 3, 2, 3) ∈ CatalanEquationSolutions := by
  simpa [mem_catalanEquationSolutions_iff] using isCatalanSolution_classic

/-- Non-example: $2^2 \neq 2^2 + 1$. -/
@[category test, AMS 11]
theorem not_isCatalanSolution_two_two : ¬ IsCatalanSolution 2 2 2 2 := by
  intro h
  norm_num [IsCatalanSolution] at h

/-- Non-example with an exponent equal to $1$ (excluded by the statement). -/
@[category test, AMS 11]
theorem not_isCatalanSolution_exp_one : ¬ IsCatalanSolution 2 3 1 3 := by
  intro h
  exact absurd h.2.2.1 (by norm_num)

end Tijdeman
