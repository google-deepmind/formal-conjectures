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
# No percolation at criticality

In Bernoulli bond percolation on a graph, each edge is kept independently with probability $p$.
The critical probability $p_c$ is the infimum of the $p$ for which an infinite cluster appears
with positive probability. The question is whether an infinite cluster can appear at $p = p_c$
itself.

On the cubic lattice $\mathbb{Z}^d$ the answer was known to be no for $d = 2$ [Ke80] and for
$d \ge 11$ [FvdH17], and on Cayley graphs of nonamenable groups [BLPS99]. Benjamini and Schramm
conjectured that it is no on every quasi-transitive graph with $p_c < 1$ [BS96]. The case of
$\mathbb{Z}^3$ was a well-known open problem.

*References:*
- [Ke80] H. Kesten, *The critical probability of bond percolation on the square lattice equals
  1/2*, Comm. Math. Phys. 74 (1980), 41–59.
- [BS96] I. Benjamini and O. Schramm, *Percolation beyond $\mathbb{Z}^d$, many questions and a
  few answers*, Electron. Comm. Probab. 1 (1996), 71–82.
- [BLPS99] I. Benjamini, R. Lyons, Y. Peres and O. Schramm, *Critical percolation on any
  nonamenable group has no infinite clusters*, Ann. Probab. 27 (1999), 1347–1356.
- [FvdH17] R. Fitzner and R. van der Hofstad, *Mean-field behavior for nearest-neighbor
  percolation in $d > 10$*, Electron. J. Probab. 22 (2017), 1–65.
- [OAI26a] OpenAI, *No percolation at criticality on quasi-transitive graphs*. OpenAI Math
  Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf
- [OAI26b] OpenAI, *Critical bond and site percolation on the cubic lattice*. OpenAI Math
  Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-bond-and-site-percolation-on-the-cubic-lattice-September-24-2026/paper.pdf
-/

@[expose] public section

namespace CriticalPercolation

open MeasureTheory ProbabilityTheory

/-- An undirected graph with labelled bonds, including loops and parallel bonds. -/
structure BondGraph (V E : Type*) where
  /-- The two endpoints of each bond. -/
  ends : E → Sym2 V

namespace BondGraph

variable {V E : Type*} (G : BondGraph V E)

/-- The graph of retained bonds. `fromEdgeSet` discards loops. -/
def openGraph (ω : Set E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' ω)

/-- The underlying connectivity graph, with every bond retained. -/
def fullGraph : SimpleGraph V := G.openGraph Set.univ

/-- Every vertex lies on finitely many bonds. -/
def LocallyFinite : Prop := ∀ v : V, {e : E | v ∈ G.ends e}.Finite

/-- Automorphisms preserve the vertex and bond structure, including multiplicities. -/
structure Aut where
  /-- The action on vertices. -/
  vertex : V ≃ V
  /-- The action on bonds. -/
  edge : E ≃ E
  preserves : ∀ e, G.ends (edge e) = Sym2.map vertex (G.ends e)

/-- The automorphism group has finitely many orbits on vertices. -/
def QuasiTransitive : Prop :=
  ∃ S : Set V, S.Finite ∧ ∀ v : V, ∃ s ∈ S, ∃ φ : G.Aut, φ.vertex s = v

/-- The open cluster of `v`: the vertices joined to `v` by a finite path of retained bonds. -/
def cluster (ω : Set E) (v : V) : Set V := {w | (G.openGraph ω).Reachable v w}

/-- The event that some open cluster is infinite. -/
def percolates : Set (Set E) := {ω | ∃ v : V, (G.cluster ω v).Infinite}

/-- Each bond is retained independently with probability `p`. -/
noncomputable def law (_G : BondGraph V E) (p : unitInterval) : Measure (Set E) :=
  ProbabilityTheory.setBernoulli Set.univ p

/-- The critical probability: the infimum of the `p` for which some cluster is infinite with
positive probability. -/
noncomputable def criticalProbability : unitInterval :=
  sInf {p : unitInterval | 0 < G.law p G.percolates}

/--
**No percolation at criticality** [BS96]: on an infinite, connected, locally finite,
quasi-transitive graph with $p_c < 1$, critical Bernoulli bond percolation has almost surely no
infinite cluster.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see OpenAI's Lean
proof.
-/
@[category research solved, AMS 60 82]
theorem no_percolation_at_criticality [Infinite V]
    (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive)
    (hpc : G.criticalProbability < 1) :
    G.law G.criticalProbability G.percolates = 0 := by
  sorry

end BondGraph

namespace Cubic

/-- The vertices of the cubic lattice $\mathbb{Z}^3$. -/
abbrev Vertex := Fin 3 → ℤ

/-- The bond `(x, i)` joins `x` to `x + eᵢ`. -/
abbrev Bond := Vertex × Fin 3

/-- A bond configuration: `true` for an open bond. -/
abbrev BondConfig := Bond → Bool

/-- A site configuration: `true` for an open site. -/
abbrev SiteConfig := Vertex → Bool

/-- `x + eᵢ`. -/
def step (x : Vertex) (i : Fin 3) : Vertex := fun j => x j + if i = j then 1 else 0

/-- `x` and `y` are nearest neighbours. -/
def NearestNeighbor (x y : Vertex) : Prop :=
  ∃ i : Fin 3, y = step x i ∨ x = step y i

/-- `x` and `y` are joined by an open bond. -/
def BondOpen (ω : BondConfig) (x y : Vertex) : Prop :=
  (∃ i : Fin 3, y = step x i ∧ ω (x, i) = true) ∨
  (∃ i : Fin 3, x = step y i ∧ ω (y, i) = true)

/-- `x` and `y` are open nearest neighbours. -/
def SiteOpen (ω : SiteConfig) (x y : Vertex) : Prop :=
  NearestNeighbor x y ∧ ω x = true ∧ ω y = true

/-- `x` and `y` are joined by a path of open bonds. -/
def BondConnected (ω : BondConfig) (x y : Vertex) : Prop :=
  Relation.ReflTransGen (BondOpen ω) x y

/-- `x` is open and joined to `y` by a path of open sites. -/
def SiteConnected (ω : SiteConfig) (x y : Vertex) : Prop :=
  ω x = true ∧ Relation.ReflTransGen (SiteOpen ω) x y

/-- The open bond cluster of `x`. -/
def bondCluster (ω : BondConfig) (x : Vertex) : Set Vertex :=
  {y | BondConnected ω x y}

/-- The open site cluster of `x`, empty if `x` is closed. -/
def siteCluster (ω : SiteConfig) (x : Vertex) : Set Vertex :=
  {y | SiteConnected ω x y}

/-- The cluster of `x` is infinite (bond percolation). -/
def bondInfiniteAt (x : Vertex) : Set BondConfig := {ω | (bondCluster ω x).Infinite}

/-- The cluster of `x` is infinite (site percolation). -/
def siteInfiniteAt (x : Vertex) : Set SiteConfig := {ω | (siteCluster ω x).Infinite}

/-- `p` clamped to `[0, 1]`. -/
noncomputable def parameter (p : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 p), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Bernoulli bond percolation with parameter `p`. -/
noncomputable def bondLaw (p : ℝ) : Measure BondConfig :=
  Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false (parameter p))

/-- Bernoulli site percolation with parameter `p`. -/
noncomputable def siteLaw (p : ℝ) : Measure SiteConfig :=
  Measure.infinitePi (fun _ : Vertex => bernoulliMeasure true false (parameter p))

/-- The critical probability of bond percolation on $\mathbb{Z}^3$. -/
noncomputable def bondCritical : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < bondLaw p (bondInfiniteAt 0)}

/-- The critical probability of site percolation on $\mathbb{Z}^3$. -/
noncomputable def siteCritical : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < siteLaw p (siteInfiniteAt 0)}

/--
**No percolation at criticality on $\mathbb{Z}^3$**: at the critical probability, bond
percolation and site percolation on $\mathbb{Z}^3$ almost surely have only finite clusters.

This was proved by an internal OpenAI model in September 2026 [OAI26b]; see OpenAI's Lean
proof.
-/
@[category research solved, AMS 60 82]
theorem critical_no_infinite :
    (∀ᵐ ω ∂bondLaw bondCritical, ∀ x : Vertex, (bondCluster ω x).Finite) ∧
    (∀ᵐ ω ∂siteLaw siteCritical, ∀ x : Vertex, (siteCluster ω x).Finite) := by
  sorry

end Cubic

end CriticalPercolation
