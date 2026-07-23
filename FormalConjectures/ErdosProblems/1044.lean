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
import FormalConjectures.ErdosProblems.«1041»

/-!
# Erdős Problem 1044

*References:*
- [erdosproblems.com/1044](https://www.erdosproblems.com/1044)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., *Metric properties of polynomials*.
  J. Analyse Math. (1958), 125-148.
- [Ta26] Tang, Quanyu, *On Erdős Problem 1044* (2026),
  [github.com/QuanyuTang/erdos-problem-1044](https://github.com/QuanyuTang/erdos-problem-1044).
-/

open Polynomial ENNReal

namespace Erdos1044

/--
The polynomials under consideration: those of the form $f(z)=\prod_{i=1}^n(z-z_i)$, for some
$n\geq 1$, where $\lvert z_i\rvert\leq 1$ for all $i$.
-/
def IsAdmissible (f : ℂ[X]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) ∧ f = ∏ i, (X - C (z i))

/--
$\Lambda(f)$, the maximum of the lengths of the boundaries of the connected components of
$\{ z: \lvert f(z)\rvert<1\}$, where the length of a subset of $\mathbb{C}$ is its
$1$-dimensional Hausdorff measure.
-/
noncomputable def maxBoundaryLength (f : ℂ[X]) : ℝ≥0∞ :=
  ⨆ z ∈ {w : ℂ | ‖f.eval w‖ < 1},
    Erdos1041.length (frontier (connectedComponentIn {w : ℂ | ‖f.eval w‖ < 1} z))

/--
Let $f(z)=\prod_{i=1}^n(z-z_i)\in\mathbb{C}[x]$ where $\lvert z_i\rvert\leq 1$ for all $i$.
If $\Lambda(f)$ is the maximum of the lengths of the boundaries of the connected components of
\[
\{ z: \lvert f(z)\rvert<1\}
\]
then determine the infimum of $\Lambda(f)$.

A problem of Erdős, Herzog, and Piranian [EHP58].

This has been resolved by Tang, who proved that the infimum of $\Lambda(f)$ over all such $f$
is $2$.
-/
@[category research solved, AMS 30]
theorem erdos_1044 :
    IsGLB {L : ℝ≥0∞ | ∃ f : ℂ[X], IsAdmissible f ∧ maxBoundaryLength f = L} answer(sorry) := by
  sorry

/--
This has been resolved by Tang, who proved that the infimum of $\Lambda(f)$ over all such $f$
is $2$.
-/
@[category research solved, AMS 30, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1044.lean"]
theorem erdos_1044.variants.infimum_eq_two :
    IsGLB {L : ℝ≥0∞ | ∃ f : ℂ[X], IsAdmissible f ∧ maxBoundaryLength f = L} 2 := by
  sorry

/--
Tang also suggests that, if the degree $n$ is fixed, then the infimum over all such $f$ of
degree $n$ is attained by $f_n(z)=z^n-1$.
-/
@[category research open, AMS 30]
theorem erdos_1044.variants.fixed_degree (n : ℕ) (hn : 0 < n) :
    IsLeast {L : ℝ≥0∞ | ∃ f : ℂ[X], IsAdmissible f ∧ f.natDegree = n ∧ maxBoundaryLength f = L}
      (maxBoundaryLength (X ^ n - 1)) := by
  sorry

/--
Tang also suggests that, if the degree $n$ is fixed, then the infimum over all such $f$ of
degree $n$ is attained by $f_n(z)=z^n-1$ (and proves this for $n=1$ and $n=2$).
-/
@[category research solved, AMS 30]
theorem erdos_1044.variants.fixed_degree_of_le_two (n : ℕ) (hn : n = 1 ∨ n = 2) :
    IsLeast {L : ℝ≥0∞ | ∃ f : ℂ[X], IsAdmissible f ∧ f.natDegree = n ∧ maxBoundaryLength f = L}
      (maxBoundaryLength (X ^ n - 1)) := by
  sorry

end Erdos1044
