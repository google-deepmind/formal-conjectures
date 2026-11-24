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
# Ben Green's Open Problem 70

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.70)
- [ABBCDHKLPW11] Abel, Z., Ballinger, B., Bose, P., Collette, S., Dujmović, V., Hurtado, F.,
  Kominers, S. D., Langerman, S., Pór, A. and Wood, D. R., *Every large point set contains many
  collinear points or an empty pentagon*. Graphs Combin. 27 (2011), 47-60.
  [arXiv:0904.0262](https://arxiv.org/abs/0904.0262)
- [KPW05] Kára, J., Pór, A. and Wood, D. R., *On the chromatic number of the visibility graph of
  a set of points in the plane*. Discrete Comput. Geom. 34 (2005), 497-506.
  [doi:10.1007/s00454-005-1177-z](https://doi.org/10.1007/s00454-005-1177-z)
- [PoWo10] Pór, A. and Wood, D. R., *On visibility and blockers*. J. Comput. Geom. 1 (2010),
  29-40. [arXiv:0912.1150](https://arxiv.org/abs/0912.1150)
-/

@[expose] public section

open scoped Finset

namespace Green70

/-- `HasCollinear k P` says that some $k$ points of `P` lie on a line. -/
def HasCollinear (k : ℕ) (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ S ⊆ P, #S = k ∧ Collinear ℝ (S : Set (ℝ × ℝ))

/--
`Visible P u v` says that the open segment between `u` and `v` contains no point of `P`. For
$u \neq v$ in `P` this means that `u` and `v` see each other: the segment joining them contains no
other point of `P`.
-/
def Visible (P : Finset (ℝ × ℝ)) (u v : ℝ × ℝ) : Prop :=
  ∀ w ∈ P, w ∉ openSegment ℝ u v

/--
`HasMutuallyVisible ℓ P` says that `P` contains $\ell$ mutually visible points: a subset `S` of
$\ell$ points such that any two distinct points of `S` see each other, with respect to all of `P`.
-/
def HasMutuallyVisible (ℓ : ℕ) (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ S ⊆ P, #S = ℓ ∧ (S : Set (ℝ × ℝ)).Pairwise (Visible P)

/--
`HasEmptyPentagon P` says that `P` contains an empty pentagon (a $5$-hole): five points of `P` in
strictly convex position, that is, none of them lies in the convex hull of the other four, such
that the convex hull of the five points contains no other point of `P`.
-/
def HasEmptyPentagon (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ S ⊆ P, #S = 5 ∧ ConvexIndependent ℝ ((↑) : ↥(S : Set (ℝ × ℝ)) → ℝ × ℝ) ∧
    ∀ p ∈ P, p ∈ convexHull ℝ (S : Set (ℝ × ℝ)) → p ∈ S

/--
Fix integers $k, \ell$. Is it true that, given a set of $n \geq n_0(k, \ell)$ points in
$\mathbb{R}^2$, either some $k$ of them lie on a line, or some $\ell$ of them are 'mutually
visible', that is to say that line segment joining them contains no other point from the set?

This question was first raised by Kára, Pór and Wood [KPW05]. It is called the big-line-big-clique
conjecture [PoWo10, Conjecture 1]. We read "mutually visible" as "pairwise visible". The cases
$k \leq 3$ are trivial: a set with no three collinear points has all pairs visible. For the
cases $\ell \leq 5$, see `green_70.variants.five_visible`.
-/
@[category research open, question, AMS 5 52]
theorem green_70 :
    ∀ k ℓ : ℕ, ∃ n₀ : ℕ, ∀ P : Finset (ℝ × ℝ),
      n₀ ≤ #P → HasCollinear k P ∨ HasMutuallyVisible ℓ P := by
  sorry

/--
The answer to `green_70` is yes for $\ell \leq 5$ [Gr24]: for every $k$, every sufficiently large
planar set contains $k$ collinear points or $5$ mutually visible points. The case $\ell = 5$ is
[ABBCDHKLPW11, Theorem 5], and it implies the cases $\ell \leq 4$ (see
`HasMutuallyVisible.mono`). According to [ABBCDHKLPW11, Section 1.4], the case $\ell = 4$ was
proved in [KPW05]. In [ABBCDHKLPW11] and [PoWo10] the letters $k$ and $\ell$ are interchanged.
-/
@[category research solved, AMS 5 52]
theorem green_70.variants.five_visible :
    ∀ k : ℕ, ∃ n₀ : ℕ, ∀ P : Finset (ℝ × ℝ),
      n₀ ≤ #P → HasCollinear k P ∨ HasMutuallyVisible 5 P := by
  sorry

/--
Generalised empty pentagon theorem [ABBCDHKLPW11, Theorem 3]: for every integer $k \geq 2$,
every sufficiently large finite set of points in the plane contains $k$ collinear points or an
empty pentagon. By `HasEmptyPentagon.hasMutuallyVisible`, this implies
`green_70.variants.five_visible`, which is [ABBCDHKLPW11, Theorem 5].
-/
@[category research solved, AMS 5 52]
theorem green_70.variants.empty_pentagon :
    ∀ k : ℕ, 2 ≤ k → ∃ n₀ : ℕ, ∀ P : Finset (ℝ × ℝ),
      n₀ ≤ #P → HasCollinear k P ∨ HasEmptyPentagon P := by
  sorry

/-- If `P` contains $\ell'$ mutually visible points, it contains $\ell$ of them for any
$\ell \leq \ell'$. -/
@[category API, AMS 5 52]
theorem HasMutuallyVisible.mono {P : Finset (ℝ × ℝ)} {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ')
    (hP : HasMutuallyVisible ℓ' P) : HasMutuallyVisible ℓ P := by
  obtain ⟨S, hSP, hcard, hvis⟩ := hP
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (show ℓ ≤ #S by omega)
  exact ⟨T, hTS.trans hSP, hTcard, hvis.mono (Finset.coe_subset.2 hTS)⟩

/-- The five corners of an empty pentagon of `P` are mutually visible. -/
@[category API, AMS 5 52]
theorem HasEmptyPentagon.hasMutuallyVisible {P : Finset (ℝ × ℝ)} (h : HasEmptyPentagon P) :
    HasMutuallyVisible 5 P := by
  obtain ⟨S, hSP, hcard, hconv, hhull⟩ := h
  refine ⟨S, hSP, hcard, ?_⟩
  intro u hu v hv huv w hw hwuv
  have hseg : w ∈ convexHull ℝ (S : Set (ℝ × ℝ)) :=
    segment_subset_convexHull (𝕜 := ℝ) hu hv (openSegment_subset_segment ℝ u v hwuv)
  have hwS : w ∈ (S : Set (ℝ × ℝ)) := hhull w hw hseg
  have hu' : u ∈ (S : Set (ℝ × ℝ)) \ {w} := by
    refine ⟨hu, ?_⟩
    intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    exact huv (left_mem_openSegment_iff.1 hwuv)
  have hv' : v ∈ (S : Set (ℝ × ℝ)) \ {w} := by
    refine ⟨hv, ?_⟩
    intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    exact huv (right_mem_openSegment_iff.1 hwuv)
  exact (convexIndependent_set_iff_notMem_convexHull_sdiff.1 hconv) w hwS
    (segment_subset_convexHull (𝕜 := ℝ) hu' hv' (openSegment_subset_segment ℝ u v hwuv))

end Green70
