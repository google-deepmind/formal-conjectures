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
# Erdős Problem 1040, part (ii)

*References:*
- [erdosproblems.com/1040](https://www.erdosproblems.com/1040)
- [EHP58] Erdős, P., Herzog, F., and Piranian, G., *Metric properties of polynomials*.
  J. Analyse Math. 6 (1958), 125–148, Problem 4, p. 135.
-/

namespace Erdos1040

open Filter MeasureTheory

/-- The unordered pairs of distinct indices, represented by increasing pairs. -/
def indexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij => ij.1 < ij.2

/-- The geometric mean of pairwise distances in a finite configuration. -/
noncomputable def vandermondeRoot (n : ℕ) (z : Fin n → ℂ) : ENNReal :=
  ENNReal.rpow
    (∏ ij ∈ indexPairs n, ENNReal.ofReal (dist (z ij.1) (z ij.2)))
    ((n.choose 2 : ℝ)⁻¹)

/-- The supremum of the pairwise-distance geometric means over configurations in F. -/
noncomputable def diameterAt (n : ℕ) (F : Set ℂ) : ENNReal :=
  ⨆ z : Fin n → ℂ, ⨆ (_ : ∀ i, z i ∈ F), vandermondeRoot n z

/-- The transfinite diameter, expressed as the limsup of finite Fekete diameters. -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ENNReal :=
  limsup (fun n => diameterAt n F) atTop

/-- The monic polynomial determined by a finite list of roots; repetitions are allowed. -/
def rootProduct (roots : List ℂ) (z : ℂ) : ℂ :=
  (roots.map fun r => z - r).prod

/-- The infimum of whole-plane strict unit-sublevel areas over nonempty root lists in F. -/
noncomputable def polynomialSublevelInfimum (F : Set ℂ) : ENNReal :=
  ⨅ roots : {l : List ℂ // l ≠ [] ∧ ∀ z ∈ l, z ∈ F},
    volume {z : ℂ | ‖rootProduct roots.1 z‖ < 1}

/--
Let $F\subseteq \mathbb{C}$ be a closed infinite set, and let $\mu(F)$ be the infimum of
$\lvert \{ z: \lvert f(z)\rvert < 1\}\rvert$, as $f$ ranges over all polynomials of the
shape $\prod (z-z_i)$ with $z_i\in F$.
In particular, is $\mu(F)=0$ whenever the transfinite diameter of $F$ is $\geq 1$?
-/
@[category research solved, AMS 30,
  formal_proof using lean4 at
    "https://github.com/WoshuaJolk/jig-verifier/blob/a23af0a9a7a426a97d5b7efd8ccc2a5a4f5eaa7c/Submissions/Erdos1040CapacityPolynomialSublevels/CapacityOne.lean"]
theorem erdos_1040.parts.ii : answer(True) ↔
    ∀ F : Set ℂ, IsClosed F → F.Infinite →
      1 ≤ transfiniteDiameter F → polynomialSublevelInfimum F = 0 := by
  sorry

end Erdos1040
