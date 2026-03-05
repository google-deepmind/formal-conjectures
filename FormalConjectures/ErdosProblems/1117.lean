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
# Erdős Problem 1117

*Reference:* [erdosproblems.com/1117](https://www.erdosproblems.com/1117)

For an entire function $f$ which is not a monomial, let $\nu(r)$ count the number of points
on the circle $|z| = r$ where $|f(z)|$ attains its maximum. Is it possible that
$\liminf_{r \to \infty} \nu(r) = \infty$?

[Ha74] Hayman, W. K., *Research Problems in Function Theory*, Athlone Press, 1967 (updated 1974).

[HePi68] Herzog, F. and Piranian, G., *Sets of radii of parity for entire functions*, 1968.

[GlPa24] Glücksam, A. and Pardo-Simón, L., *An approximate answer to a question of Erdős*, 2024.
-/

open Complex Set

namespace Erdos1117

/-- A function $f : \mathbb{C} \to \mathbb{C}$ is a monomial if $f(z) = c \cdot z^n$ for some
constant $c$ and natural number $n$. -/
def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (n : ℕ), ∀ z, f z = c * z ^ n

/-- The maximum modulus of $f$ on the circle of radius $r$:
$M(r) = \sup\{\|f(z)\| : \|z\| = r\}$. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- $\nu(r)$ counts the number of $z$ with $\|z\| = r$ achieving the maximum modulus
of $f$. This is finite when $f$ is entire and not a monomial. -/
noncomputable def nu (f : ℂ → ℂ) (r : ℝ) : ℕ :=
  Set.ncard {z : ℂ | ‖z‖ = r ∧ ‖f z‖ = maxModulus f r}

/--
Erdős Problem 1117 [Ha74]

Let $f(z)$ be an entire function which is not a monomial. Let $\nu(r)$ count the
number of $z$ with $|z| = r$ such that $|f(z)| = \max_{|z|=r} |f(z)|$.
(This is a finite quantity if $f$ is not a monomial.)

Is it possible for $\liminf_{r \to \infty} \nu(r) = \infty$?

The analogous question for $\limsup$ was answered affirmatively by Herzog and
Piranian [HePi68]. The $\liminf$ question remains open. An 'approximate'
affirmative answer is given by Glücksam and Pardo-Simón [GlPa24].
-/
@[category research open, AMS 30]
theorem erdos_1117 : answer(sorry) ↔
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ¬IsMonomial f ∧
      ∀ N : ℕ, ∃ R : ℝ, ∀ r : ℝ, R ≤ r → N ≤ nu f r := by
  sorry

end Erdos1117
