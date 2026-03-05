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
# Erdős Problem 365

*Reference:* [erdosproblems.com/365](https://www.erdosproblems.com/365)

[Er76d] Erdős, P., *Problems in number theory and combinatorics*, Proc. 6th Manitoba Conf. on
Numerical Mathematics (1976), p. 31.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*, Monographies de L'Enseignement Mathematique (1980), p. 68.

[Go70] Golomb, S.W., *Powerful numbers*, Amer. Math. Monthly 77 (1970), 848–852.

[Wa76] Walker, D.T., *Consecutive integer pairs of powerful numbers and related Diophantine
equations*, Fibonacci Quart. 14 (1976), 111–116.
-/

open Finset Real

namespace Erdos365

/-- A positive integer $n$ is *powerful* (also called squarefull) if for every
prime $p$ dividing $n$, $p^2$ also divides $n$. -/
def IsPowerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Erdős Problem 365 [Er76d, p. 31] [ErGr80, p. 68]:

Do all pairs of consecutive powerful numbers $n$ and $n+1$ come from solutions to
Pell equations? In other words, must either $n$ or $n+1$ be a square?

Is the number of such $n \leq x$ bounded by $(\log x)^{O(1)}$?

The first question was answered negatively by Golomb [Go70], who observed that
$12167 = 23^3$ and $12168 = 2^3 \cdot 3^2 \cdot 13^2$ are both powerful (neither is a square).
Walker [Wa76] proved that $7^3 x^2 = 3^3 y^2 + 1$ has infinitely many solutions,
giving infinitely many counterexamples.

The second question remains open. We formalize it: there exists $C > 0$ such that
for all sufficiently large $x$, the number of $n \leq x$ with both $n$ and $n+1$ powerful
is at most $(\log x)^C$.
-/
@[category research open, AMS 11]
theorem erdos_365 : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 x →
          (∀ n ∈ S, IsPowerful n ∧ IsPowerful (n + 1)) →
          (S.card : ℝ) ≤ (Real.log (x : ℝ)) ^ C := by
  sorry

end Erdos365
