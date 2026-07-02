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
# Erdős Problem 224

*References:*
- [erdosproblems.com/224](https://www.erdosproblems.com/224)
- [DaGr62] Danzer, L. and Gr\"{u}nbaum, B., *\"{U}ber zwei Probleme
  bez\"{u}glich konvexer K\"{o}rper von P. Erd\H{o}s und von V. L. Klee*.
  Math. Z. (1962), 95-99.
-/

namespace Erdos224

open scoped EuclideanGeometry

/-- The angle $yxz$ is obtuse. -/
def ObtuseAt {d : ℕ} (x y z : ℝ^d) : Prop :=
  inner ℝ (y - x) (z - x) < 0

/--
If $A\subseteq \mathbb{R}^d$ is any set of $2^d+1$ points then some three points in $A$ determine an obtuse angle.

The general case was proved by Danzer and Gr\"{u}nbaum [DaGr62].
-/
@[category research solved, AMS 52,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos224.lean"]
theorem erdos_224 {d : ℕ} (A : Finset (ℝ^d)) (hcard : A.card = 2 ^ d + 1) :
    ∃ x y z : ℝ^d, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ObtuseAt x y z := by
  sorry

end Erdos224
