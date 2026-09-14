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
# Erdős Problem 798

*References:*
- [erdosproblems.com/798](https://www.erdosproblems.com/798)
- [Al91] Alon, N., *Economical coverings of sets of lattice points*. Geom. Funct. Anal. (1991),
  224-230.
-/

namespace Erdos798

open Filter Asymptotics

/--
The grid $\{1,\ldots,n\}^2$, viewed as a set of points of the plane.
-/
def gridPoints (n : ℕ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | ∃ i j : ℕ, 1 ≤ i ∧ i ≤ n ∧ 1 ≤ j ∧ j ≤ n ∧ p = ((i : ℝ), (j : ℝ))}

/--
`S` is a set of points of $\{1,\ldots,n\}^2$ such that the lines determined by the pairs of
distinct points of `S` cover all points of $\{1,\ldots,n\}^2$.
-/
def IsLineCover (n : ℕ) (S : Set (ℝ × ℝ)) : Prop :=
  S ⊆ gridPoints n ∧
    ∀ x ∈ gridPoints n, ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ Collinear ℝ ({p, q, x} : Set (ℝ × ℝ))

/--
The minimum number of points in $\{1,\ldots,n\}^2$ such that the lines determined by these points
cover all points in $\{1,\ldots,n\}^2$.
-/
noncomputable def t (n : ℕ) : ℕ :=
  sInf {k | ∃ S : Set (ℝ × ℝ), IsLineCover n S ∧ S.ncard = k}

/--
Let $t(n)$ be the minimum number of points in $\{1,\ldots,n\}^2$ such that the $\binom{t}{2}$
lines determined by these points cover all points in $\{1,\ldots,n\}^2$.

Estimate $t(n)$. In particular, is it true that $t(n)=o(n)$?

A problem of Erdős and Purdy, who proved $t(n) \gg n^{2/3}$.

Resolved by Alon [Al91] who proved $t(n) \ll n^{2/3}\log n$.
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos798.lean"]
theorem erdos_798 : answer(True) ↔
    (fun n : ℕ => (t n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

/--
A problem of Erdős and Purdy, who proved $t(n) \gg n^{2/3}$.
-/
@[category research solved, AMS 5 52]
theorem erdos_798.variants.lower_bound :
    (fun n : ℕ => (n : ℝ) ^ (2 / 3 : ℝ)) =O[atTop] (fun n : ℕ => (t n : ℝ)) := by
  sorry

/--
Resolved by Alon [Al91] who proved $t(n) \ll n^{2/3}\log n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_798.variants.upper_bound :
    (fun n : ℕ => (t n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (2 / 3 : ℝ) * Real.log n) := by
  sorry

end Erdos798
