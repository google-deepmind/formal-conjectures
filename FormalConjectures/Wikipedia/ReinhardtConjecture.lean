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
# The Reinhardt conjecture

Reinhardt conjectured in 1934 that the *smoothed octagon* has the least greatest packing density
among all centrally symmetric convex disks in the plane. The smoothed octagon is a regular octagon
whose corners are cut off by arcs of hyperbolas. Its greatest packing density is
$$\delta_{oct} = \frac{8 - 4\sqrt{2} - \log 2}{2\sqrt{2} - 1} = 0.902414\ldots,$$
and the conjecture includes that it is the only worst disk up to affine maps.
Mahler reached the same octagon independently in 1947.

The definitions follow [HaVa24, Definition 2.1.1]. Points of the plane are `Fin 2 → ℝ`, and areas
are Lebesgue measure. Since `Fin 2 → ℝ` carries the sup norm, the Euclidean disk is written out.

*References:*
- [Wikipedia, Smoothed octagon](https://en.wikipedia.org/wiki/Smoothed_octagon)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Re34] Reinhardt, K. _Über die dichteste gitterförmige Lagerung kongruenter Bereiche in der
  Ebene und eine besondere Art konvexer Kurven_. Abh. Math. Sem. Univ. Hamburg 10 (1934), 216–230.
  [doi:10.1007/BF02940676](https://doi.org/10.1007/BF02940676)
- [Ma47] Mahler, K. _On the minimum determinant and the circumscribed hexagons of a convex
  domain_. Proc. Kon. Ned. Akad. Wetensch. 50 (1947), 692–703.
- [Ha11] Hales, T. C. _On the Reinhardt conjecture_. Vietnam J. Math. 39 (2011), 287–307.
  [arXiv:1103.4518](https://arxiv.org/abs/1103.4518)
- [HaVa24] Hales, T. C. and Vajjha, K. _Packings of smoothed polygons_ (2024).
  [arXiv:2405.04331](https://arxiv.org/abs/2405.04331)
- [The-Anh Vu-Le, Lean 4 proof of the Reinhardt conjecture](https://github.com/vltanh/lean4-smoothed-octagon/tree/9ba6bf8630c70d6a0f11ecfef15021cb83df8c40),
  registered on Palomar as
  [PALOMAR-2026-11-09-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-09-000008)
-/

@[expose] public section

namespace ReinhardtConjecture

open MeasureTheory

/-- A **convex disk** is a compact convex set with nonempty interior. -/
def IsConvexDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- The Euclidean disk $B_r = \{x \mid x_0^2 + x_1^2 \le r^2\}$ of radius $r$ centred at the
origin. -/
def euclidDisk (r : ℝ) : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2}

/-- $K'$ is a **congruent copy** of $K$ if $K' = \{Ax + b \mid x \in K\}$ for an orthogonal
matrix $A$ and a vector $b$. -/
def IsCongruentCopy (K K' : Set (Fin 2 → ℝ)) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin 2) ℝ, ∃ b : Fin 2 → ℝ, K' = (fun x ↦ Matrix.mulVec A x + b) '' K

/-- A **packing** is a family of convex disks with pairwise disjoint interiors. -/
def IsPacking (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  (∀ K' ∈ P, IsConvexDisk K') ∧ P.Pairwise fun A B ↦ Disjoint (interior A) (interior B)

/-- A packing by congruent copies of $K$. -/
def IsPackingOfCopies (K : Set (Fin 2 → ℝ)) (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  IsPacking P ∧ ∀ K' ∈ P, IsCongruentCopy K K'

/-- The fraction $\frac{1}{\operatorname{area}(B_r)} \sum_{K' \in P} \operatorname{area}(K' \cap B_r)$
of the disk $B_r$ covered by $P$, in $[0, \infty]$. -/
noncomputable def packingRatio (P : Set (Set (Fin 2 → ℝ))) (r : ℝ) : ENNReal :=
  (∑' K' : P, volume ((K' : Set (Fin 2 → ℝ)) ∩ euclidDisk r)) / volume (euclidDisk r)

/-- The upper density of a packing, the $\limsup$ of `packingRatio P r` as $r \to \infty$. -/
noncomputable def upperDensity (P : Set (Set (Fin 2 → ℝ))) : ENNReal :=
  Filter.limsup (packingRatio P) Filter.atTop

/-- The lower density of a packing, the $\liminf$ of `packingRatio P r` as $r \to \infty$. -/
noncomputable def lowerDensity (P : Set (Set (Fin 2 → ℝ))) : ENNReal :=
  Filter.liminf (packingRatio P) Filter.atTop

/-- The density of $P$ exists if the upper density is finite and equals the lower density. -/
def HasDensity (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  upperDensity P ≠ ⊤ ∧ upperDensity P = lowerDensity P

/-- The density $\delta(K, P)$ of a packing. It is meaningful when `HasDensity P` holds. -/
noncomputable def packingDensity (P : Set (Set (Fin 2 → ℝ))) : ℝ :=
  (upperDensity P).toReal

/-- The **greatest packing density** $\delta(K)$: the supremum of $\delta(K, P)$ over the packings
$P$ by congruent copies of $K$ whose density exists. -/
noncomputable def greatestPackingDensity (K : Set (Fin 2 → ℝ)) : ℝ :=
  sSup {d | ∃ P, IsPackingOfCopies K P ∧ HasDensity P ∧ packingDensity P = d}

/-- The distance $d_k(x) = 1 - (x_0 \cos(k\pi/4) + x_1 \sin(k\pi/4))$ from $x$ to the line of the
$k$-th side of the regular octagon of inradius $1$, positive on the side of the origin. -/
noncomputable def octagonSideDist (k : Fin 8) (x : Fin 2 → ℝ) : ℝ :=
  1 - (x 0 * Real.cos ((k : ℕ) * Real.pi / 4) + x 1 * Real.sin ((k : ℕ) * Real.pi / 4))

/-- **Reinhardt's smoothed octagon**: the regular octagon $d_k \ge 0$ of inradius $1$ with each
corner cut off by an arc of a hyperbola. The corner between sides $k$ and $k + 1$ is cut off
along the hyperbola $d_{k-1} d_{k+2} = \sqrt{2}/4$, whose asymptotes are the next two side lines.
The arc touches the two sides where $d_k + d_{k+1} = 3/2 - \sqrt{2}$. -/
def smoothedOctagon : Set (Fin 2 → ℝ) :=
  {x | ∀ k : Fin 8, 0 ≤ octagonSideDist k x ∧
    (octagonSideDist k x + octagonSideDist (k + 1) x ≤ 3 / 2 - √2 →
      √2 / 4 ≤ octagonSideDist (k - 1) x * octagonSideDist (k + 2) x)}

/-- The centre of the smoothed octagon lies in it. -/
@[category test, AMS 52]
theorem zero_mem_smoothedOctagon : 0 ∈ smoothedOctagon := by
  intro k
  have h : (3 : ℝ) / 2 - √2 < 1 + 1 := by linarith [Real.sqrt_nonneg 2]
  simp only [octagonSideDist, Pi.zero_apply, zero_mul, add_zero, sub_zero]
  exact ⟨zero_le_one, fun h' ↦ absurd h' (not_le.2 h)⟩

/-- The smoothed octagon is a centrally symmetric convex disk of greatest packing density
$\delta_{oct} = (8 - 4\sqrt{2} - \log 2)/(2\sqrt{2} - 1)$ [Re34], [Ma47]. -/
@[category research solved, AMS 52,
  formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-09-000008"]
theorem octagon_density :
    IsConvexDisk smoothedOctagon ∧ (∀ x ∈ smoothedOctagon, -x ∈ smoothedOctagon) ∧
      greatestPackingDensity smoothedOctagon = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  sorry

/-- **The Reinhardt conjecture.** Every centrally symmetric convex disk in the plane has greatest
packing density at least $\delta_{oct}$, the density of the smoothed octagon [Re34]. -/
@[category research solved, AMS 52,
  formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-09-000008"]
theorem reinhardt (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ greatestPackingDensity K := by
  sorry

/-- **The equality case.** A centrally symmetric convex disk has greatest packing density
$\delta_{oct}$ if and only if it is the image of the smoothed octagon under an invertible affine
map of the plane [Re34]. -/
@[category research solved, AMS 52,
  formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-09-000008"]
theorem reinhardt_equality (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ↔
      ∃ A : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ), K = A '' smoothedOctagon := by
  sorry

end ReinhardtConjecture
