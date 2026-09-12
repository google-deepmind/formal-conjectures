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
# Erdős Problem 1164

*Reference:* [erdosproblems.com/1164](https://www.erdosproblems.com/1164)
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos1164

/-- The closed Euclidean disc of radius `R` in the integer lattice $\mathbb{Z}^2$. -/
def latticeDisc (R : ℕ) : Set (ℤ × ℤ) :=
  { p | (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ R ^ 2 }

/-- A walk of length `n` on $\mathbb{Z}^2$ starting at the origin, with steps of length 1
in the axis directions. -/
def IsSimpleWalk (n : ℕ) (w : Fin (n + 1) → ℤ × ℤ) : Prop :=
  w 0 = 0 ∧
    ∀ i : Fin n,
      ((w i.succ).1 - (w i.castSucc).1) ^ 2 + ((w i.succ).2 - (w i.castSucc).2) ^ 2 = 1

/-- The walk visits every lattice point of the disc of radius `R`. -/
def VisitsDisc (n R : ℕ) (w : Fin (n + 1) → ℤ × ℤ) : Prop :=
  ∀ p ∈ latticeDisc R, ∃ i, w i = p

/-- The proportion of simple walks of length `n` that visit the disc of radius `R`. -/
noncomputable def visitProportion (n R : ℕ) : ℝ :=
  let walks := { w : Fin (n + 1) → ℤ × ℤ | IsSimpleWalk n w }
  let good := { w : Fin (n + 1) → ℤ × ℤ | IsSimpleWalk n w ∧ VisitsDisc n R w }
  (good.ncard : ℝ) / (walks.ncard : ℝ)

/-- $R_n$: maximal `R` such that `visitProportion n R = 1` (every simple walk of length `n`
visits the disc). The problem's "almost every" is recovered as this maximal radius; for the
asymptotic the difference between "all" and "almost all" is absorbed in the $\asymp$. -/
noncomputable def R (n : ℕ) : ℕ :=
  sSup { r : ℕ | visitProportion n r = 1 }

/--
Let $R_n$ be the maximal integer such that almost every random walk from the origin in
$\mathbb{Z}^2$ visits every $x\in\mathbb{Z}^2$ with $\| x\|\leq R_n$ in at most $n$ steps.
Is it true that
$$
\log R_n \asymp \sqrt{\log n}?
$$
-/
@[category research open, AMS 60]
theorem erdos_1164 :
    answer(sorry) ↔
      (fun n : ℕ ↦ Real.log (R n)) =Θ[atTop]
        fun n : ℕ ↦ Real.sqrt (Real.log n) := by
  sorry

end Erdos1164
