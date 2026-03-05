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
# Erdős Problem 1116

*Reference:* [erdosproblems.com/1116](https://www.erdosproblems.com/1116)

For a meromorphic function $f$, let $n(r,a)$ count the number of roots of $f(z) = a$
in the disc $|z| < r$. Does there exist a meromorphic (or entire) $f$ such that
for every $a \neq b$, $\limsup_{r\to\infty} n(r,a)/n(r,b) = \infty$?
Solved affirmatively by Gol'dberg [Go78] and Toppila [To76].

[Go78] Gol'dberg, A. A., *On the deficiencies of meromorphic functions* (1978).

[To76] Toppila, S., *On Nevanlinna's second theorem and deficient values* (1976).
-/

open Complex Set

namespace Erdos1116

/-- The counting function $n(r, a, f)$: the number of solutions to $f(z) = a$
in the open disk $\{z \in \mathbb{C} \mid \|z\| < r\}$. Uses `Set.ncard` (natural cardinality). -/
noncomputable def rootCount (f : ℂ → ℂ) (r : ℝ) (a : ℂ) : ℕ :=
  Set.ncard {z : ℂ | f z = a ∧ ‖z‖ < r}

/--
Erdős Problem 1116 (Solved by Gol'dberg [Go78] and Toppila [To76]):

For a meromorphic function $f$, let $n(r,a)$ count the number of roots of $f(z) = a$
in the disc $|z| < r$. Does there exist a meromorphic (or entire) $f$ such that
for every $a \neq b$, $\limsup_{r\to\infty} n(r,a)/n(r,b) = \infty$?

Gol'dberg and Toppila independently constructed entire functions with this property.

The $\limsup = \infty$ condition is expressed multiplicatively: for every $M$ and $R$,
there exists $r > R$ with $n(r,a) > M \cdot n(r,b)$.
-/
@[category research solved, AMS 30]
theorem erdos_1116 : answer(True) ↔
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ a b : ℂ, a ≠ b →
        ∀ (M : ℝ) (R : ℝ), ∃ r : ℝ, r > R ∧
          M * (rootCount f r b : ℝ) < (rootCount f r a : ℝ) := by
  sorry

end Erdos1116
