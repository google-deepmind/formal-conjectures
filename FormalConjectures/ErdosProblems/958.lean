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
# Erdős Problem 958

*References:*
- [erdosproblems.com/958](https://www.erdosproblems.com/958)
- [CDL25] Clemen, F., Dumitrescu, A. and Liu, D., *On multiplicities of interpoint distances*.
  arXiv:2505.04283 (2025).
-/

open Finset EuclideanGeometry

namespace Erdos958

/-- The set of distances determined by a finite set of points `A` in the plane. -/
noncomputable def distanceSet (A : Finset ℝ²) : Finset ℝ :=
  A.offDiag.image fun p => dist p.1 p.2

/-- The multiplicity of the distance `d` determined by `A`, that is, the number of unordered
pairs of distinct points of `A` at distance `d` apart. -/
noncomputable def distanceMultiplicity (A : Finset ℝ²) (d : ℝ) : ℕ :=
  #(A.offDiag.filter (fun p => dist p.1 p.2 = d)) / 2

/-- `A` is a set of equidistant points on a line: there are a point `a` and a non-zero direction
`v` such that `A` consists of the points `a + i • v` for `0 ≤ i < #A`. -/
def IsEquidistantOnLine (A : Finset ℝ²) : Prop :=
  ∃ a v : ℝ², v ≠ 0 ∧ (A : Set ℝ²) = {x | ∃ i : ℕ, i < #A ∧ x = a + (i : ℝ) • v}

/-- `A` is a set of equidistant points on a circle: there are a centre `c`, a radius `r > 0`, an
initial angle `θ` and a non-zero angular step `α` such that `A` consists of the points of the
circle of centre `c` and radius `r` at the angles `θ + i * α` for `0 ≤ i < #A`. -/
def IsEquidistantOnCircle (A : Finset ℝ²) : Prop :=
  ∃ (c : ℝ²) (r θ α : ℝ), 0 < r ∧ α ≠ 0 ∧ (A : Set ℝ²) =
    {x | ∃ i : ℕ, i < #A ∧
      x = c + r • (!₂[Real.cos (θ + (i : ℝ) * α), Real.sin (θ + (i : ℝ) * α)])}

/--
Let $A\subset \mathbb{R}^2$ be a finite set of size $n$, and let $\{d_1,\ldots,d_k\}$ be the set of
distances determined by $A$. Let $f(d)$ be the multiplicity of $d$, that is, the number of
unordered pairs from $A$ of distance $d$ apart.

Is it true that $k=n-1$ and $\{f(d_i)\}=\{n-1,\ldots,1\}$ if and only if $A$ is a set of
equidistant points on a line or a circle?

Erdős conjectured that the answer is no, and other such configurations exist.

This was proved by Clemen, Dumitrescu, and Liu [CDL25], who observed that equidistant points on a
short circular arc on a circle of radius $1$, together with the centre, are also an example.
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos958.lean"]
theorem erdos_958 : answer(False) ↔
    ∀ (n : ℕ) (A : Finset ℝ²), #A = n →
      ((#(distanceSet A) = n - 1 ∧
            (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) →
        (IsEquidistantOnLine A ∨ IsEquidistantOnCircle A)) := by
  sorry

end Erdos958
