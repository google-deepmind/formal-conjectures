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
module

public import FormalConjecturesUtil

/-!
# Radenković–Gutman path-minimum problem for Laplacian energy

*References:*
- [S. Radenković and I. Gutman, Total π-electron energy and Laplacian energy: how far the analogy goes?, Rule 2 (2007)](https://www.shd.org.rs/JSCS/Vol72/No12/JSCS_V72_No12-18.pdf)
- [J. J. Gebendorfer, Laplacian energy of trees and pendant-path fusion: A computer-assisted proof of the Radenković–Gutman conjecture, 5 September 2026](https://doi.org/10.5281/zenodo.22342611)
- [Partial Lean reductions and reproduction instructions](https://github.com/RhudeJJJJ/formal-conjectures/blob/758afccf094d20534eb7be08297b0e5a22111aae/Proofs/RG_Lean_20261019/README.md)

The written universal proof uses computer-assisted analytic certificates. Their
reproduction and the existing partial Lean infrastructure do not by themselves
constitute a universal Lean proof. The already-known star upper bound is a
separate credited result and is not the contribution targeted by this module.
-/

@[expose] public section
namespace RadenkovicGutman
open SimpleGraph

/-- All Laplacian eigenvalues, with multiplicities, centered at the actual mean
degree 2m/n. The energy is a real sum of absolute deviations. -/
noncomputable def laplacianEnergy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ := by
  classical
  exact ∑ v : V, |(G.isHermitian_lapMatrix ℝ).eigenvalues v -
    2 * (G.edgeFinset.card : ℝ) / Fintype.card V|

/-- The path minimizes Laplacian energy among finite trees of every positive
order, including the one-vertex tree. -/
@[category research solved, AMS 5 15]
theorem path_minimum (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) :
    laplacianEnergy (pathGraph n) ≤ laplacianEnergy T := by
  sorry

/-- Equality occurs precisely for the path, independently of vertex labels. -/
@[category research solved, AMS 5 15]
theorem path_equality (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) :
    laplacianEnergy T = laplacianEnergy (pathGraph n) ↔
      Nonempty (T ≃g pathGraph n) := by
  sorry

end RadenkovicGutman
