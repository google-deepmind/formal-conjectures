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
# Boundary vertex conjecture for minimal lattice covering bodies

A **lattice covering body** with respect to a full-rank lattice $\Lambda \subset \mathbb{R}^n$ is a compact convex
body $K$ whose translates by $\Lambda$ tile all of $\mathbb{R}^n$ (i.e. $K + \Lambda = \mathbb{R}^n$). A **minimal covering
body** (MB) is one for which no strictly smaller compact convex subset also covers.

**Conjecture 3.3 (Lian–Xue, 2026):** If $K + \Lambda$ is a minimal covering of $\mathbb{R}^n$ and $K$
contains a translation $Q + x$ of a full-dimensional lattice polytope $Q$ (i.e. a polytope
whose vertices all lie in $\Lambda$ and whose interior is non-empty), then every vertex of $Q + x$
lies on the topological boundary $\partial K$.

*References:*
- Yanlu Lian, Fei Xue,
  [Minimal Covering Bodies and a Minkowski-Type Criterion for Lattice Coverings](https://arxiv.org/abs/2606.14584),
  arXiv:2606.14584, Conjecture 3.3 (page 11).
- [OpenConjecture ID 3747](https://github.com/davisrbr/conjectures-arxiv)
-/

namespace Arxiv.«2606.14584»

open Set Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- A set $K$ is a **lattice covering body** with respect to the additive subgroup $\Lambda$ if the
family of translates $\{K + v \mid v \in \Lambda\}$ covers all of $E$, i.e. $K + \Lambda = E$. -/
def IsLatticeCoveringBody (Λ : AddSubgroup E) (K : Set E) : Prop :=
  ∀ x : E, ∃ v ∈ Λ, x ∈ K + {v}

/-- A compact convex body $K$ is a **minimal covering body** with respect to the lattice $\Lambda$ if:
1. $K$ is a lattice covering body, and
2. No strictly smaller compact convex subset $K' \subsetneq K$ is also a lattice covering body. -/
def IsMinimalCoveringBody (Λ : AddSubgroup E) (K : Set E) : Prop :=
  IsLatticeCoveringBody Λ K ∧
  IsCompact K ∧
  Convex ℝ K ∧
  ∀ K' : Set E, K' ⊆ K → K' ≠ K → IsCompact K' → Convex ℝ K' →
    ¬IsLatticeCoveringBody Λ K'

/-- A set $Q$ is a **full-dimensional lattice polytope** with respect to $\Lambda$ if it is the convex
hull of finitely many points of $\Lambda$ and has non-empty interior (i.e. has dimension $n$). -/
def IsFullDimLatticePolytope (Λ : AddSubgroup E) (Q : Set E) : Prop :=
  ∃ s : Finset E, (∀ v ∈ s, v ∈ Λ) ∧ Q = convexHull ℝ ↑s ∧ (interior Q).Nonempty

/-- **Conjecture 3.3 (Lian–Xue, 2026).**

Let $E = \mathbb{R}^n$, $\Lambda$ a full-rank lattice in $E$, and $K$ a minimal covering body for $\Lambda$.
Suppose $Q$ is a full-dimensional lattice polytope (vertices in $\Lambda$, $\dim Q = n$) and
$x \in E$ is a translation vector such that $Q + x \subseteq K$. Then every vertex $w$ of the
translated polytope $Q + x$ lies on the topological boundary $\partial K$ of $K$. -/
@[category research open, AMS 52]
theorem boundary_vertex_conjecture
    {Λ : AddSubgroup E} {K : Set E}
    (hK : IsMinimalCoveringBody Λ K)
    {Q : Set E} (hQ : IsFullDimLatticePolytope Λ Q)
    {x : E} (hQx : {y + x | y ∈ Q} ⊆ K)
    {w : E} (hw : w ∈ (convexHull ℝ {y + x | y ∈ Q}).extremePoints ℝ) :
    w ∈ frontier K := by
  sorry

end Arxiv.«2606.14584»
