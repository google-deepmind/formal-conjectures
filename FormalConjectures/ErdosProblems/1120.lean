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
# Erdős Problem 1120

*References:*
- [erdosproblems.com/1120](https://www.erdosproblems.com/1120)
- [Ha74] Hayman, W. K., Research problems in function theory: new problems. (1974), 155--180.
-/

open Polynomial MeasureTheory ENNReal Filter

namespace Erdos1120

/--
The length of a subset $s$ of $\mathbb{C}$ is defined to be its $1$-dimensional
Hausdorff measure $\mathcal{H}^1(s)$.
-/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/--
The closed sublevel set $E_f = \{ z : \lvert f(z)\rvert \leq 1 \}$.
-/
def sublevel (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ ≤ 1}

/--
A monic polynomial of degree $n$ whose roots all lie in the closed unit disk.
-/
def IsAdmissible (n : ℕ) (f : ℂ[X]) : Prop :=
  f.Monic ∧ f.natDegree = n ∧ f.rootSet ℂ ⊆ Metric.closedBall 0 1

/--
The infimum of $\mathcal{H}^1(\mathrm{range}(\gamma))$ over paths $\gamma$ in $E_f$ from
$z = 0$ to the unit circle $\lvert z\rvert = 1$. If no such path exists, this is $\infty$.
-/
noncomputable def shortestPathLength (f : ℂ[X]) : ℝ≥0∞ :=
  ⨅ (z : ℂ) (γ : Path (0 : ℂ) z) (_ : ‖z‖ = 1) (_ : Set.range γ ⊆ sublevel f),
    length (Set.range γ)

/--
The worst-case shortest path length $S(n)$: the supremum of `shortestPathLength f` over
admissible polynomials of degree $n$.
-/
noncomputable def worstCase (n : ℕ) : ℝ≥0∞ :=
  ⨆ (f : ℂ[X]) (_ : IsAdmissible n f), shortestPathLength f

/--
Let $f\in \mathbb{C}[z]$ be a monic polynomial of degree $n$, all of whose roots satisfy
$\lvert z\rvert\leq 1$. Let
$$E= \{ z : \lvert f(z)\rvert \leq 1\}.$$
What is the shortest length of a path in $E$ joining $z=0$ to $\lvert z\rvert =1$?

This is Problem 4.22 in [Ha74], where it is attributed to Erdős. The interesting side of
the question is the worst-case behaviour as a function of $n$. Path length is measured by
$1$-dimensional Hausdorff measure, as in [Erdős Problem 1041](https://www.erdosproblems.com/1041).
-/
@[category research open, AMS 12 30]
theorem erdos_1120 (n : ℕ) : answer(sorry) = worstCase n := by
  sorry

/--
Clunie and Netanyahu (personal communication, reported in [Ha74]) showed that a path
always exists in $E_f$ joining $z = 0$ to $\lvert z\rvert = 1$.
-/
@[category research solved, AMS 12 30]
theorem erdos_1120.variants.path_exists (n : ℕ) (f : ℂ[X]) (hf : IsAdmissible n f) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ γ : Path (0 : ℂ) z, Set.range γ ⊆ sublevel f := by
  sorry

/--
The trivial lower bound for the length of this path is $1$.
-/
@[category research solved, AMS 12 30]
theorem erdos_1120.variants.lower_bound (n : ℕ) (f : ℂ[X]) (hf : IsAdmissible n f) :
    1 ≤ shortestPathLength f := by
  sorry

/--
The lower bound $1$ is achieved for $f(z) = z^n$.
-/
@[category research solved, AMS 12 30]
theorem erdos_1120.variants.monomial (n : ℕ) : shortestPathLength (X ^ n) = 1 := by
  sorry

/--
Erdős wrote 'presumably this tends to infinity with $n$, but not too fast'.
-/
@[category research open, AMS 12 30]
theorem erdos_1120.variants.tends_to_infinity :
    ∀ M : ℝ, ∀ᶠ n : ℕ in atTop, ENNReal.ofReal M ≤ worstCase n := by
  sorry

end Erdos1120
