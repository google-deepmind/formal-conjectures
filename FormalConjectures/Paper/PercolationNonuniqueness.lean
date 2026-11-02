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
# Nonuniqueness of percolation on nonamenable Cayley graphs

In Bernoulli bond percolation with parameter $p$, the critical probability $p_c$ is the infimum
of the $p$ for which an infinite cluster appears, and the uniqueness threshold $p_u$ is the
infimum of the $p$ for which there is almost surely exactly one infinite cluster. Benjamini and
Schramm conjectured that $p_c < p_u$ on every nonamenable quasi-transitive graph, so that there
is a phase with infinitely many infinite clusters [BS96].

Pak and Smirnova-Nagnibeda showed that every nonamenable group has some Cayley graph with
$p_c < p_u$ [PSN00]. Hutchcroft proved the conjecture for Gromov hyperbolic graphs [Hu19].

*References:*
- [BS96] I. Benjamini and O. Schramm, *Percolation beyond $\mathbb{Z}^d$, many questions and a
  few answers*, Electron. Comm. Probab. 1 (1996), 71–82.
- [PSN00] I. Pak and T. Smirnova-Nagnibeda, *On non-uniqueness of percolation on nonamenable
  Cayley graphs*, C. R. Acad. Sci. Paris Sér. I Math. 330 (2000), 495–500.
- [Hu19] T. Hutchcroft, *Percolation on hyperbolic graphs*, Geom. Funct. Anal. 29 (2019),
  766–810.
- [OAI26] OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs*. OpenAI
  Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf
-/

@[expose] public section

namespace PercolationNonuniqueness

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u v
variable {V : Type u} {E : Type v}

/-- A graph with labelled bonds: each bond has two endpoints. -/
abbrev BondGraph (V : Type u) (E : Type v) := E → Sym2 V

/-- `x` and `y` are joined by a path of bonds in `ω`. -/
def Conn (G : BondGraph V E) (ω : Set E) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ e ∈ ω, G e = s(a, b)) x y

/-- The open cluster of `x`. -/
def cluster (G : BondGraph V E) (ω : Set E) (x : V) : Set V :=
  {y | Conn G ω x y}

/-- The infinite open clusters. -/
def infiniteClusters (G : BondGraph V E) (ω : Set E) : Set (Set V) :=
  {C | C.Infinite ∧ ∃ x, C = cluster G ω x}

/-- Each bond is retained independently with probability `p`. -/
noncomputable def law (p : unitInterval) : Measure (Set E) :=
  setBernoulli Set.univ p

/-- The critical probability: the infimum of the `p` for which an infinite cluster appears
with positive probability. -/
noncomputable def pc (G : BondGraph V E) : unitInterval :=
  sInf {p | 0 < law p {ω | (infiniteClusters G ω).Nonempty}}

/-- The uniqueness threshold: the infimum of the `p` for which there is almost surely exactly
one infinite cluster. -/
noncomputable def pu (G : BondGraph V E) : unitInterval :=
  sInf {p | law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 1}

/-- The probability that `x` and `y` are in the same cluster. -/
noncomputable def twoPoint (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  (law p {ω | Conn G ω x y}).toReal

/-- `ℓ²(V)`. -/
noncomputable abbrev Hilbert (V : Type u) := lp (fun _ : V => ℂ) 2

/-- `A` has matrix entries `A(x, y) = τ_p(x, y)`. -/
noncomputable def HasKernel [DecidableEq V]
    (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ x y, (A (lp.single 2 y (1 : ℂ))) x = (twoPoint G p x y : ℂ)

/-- The two-point matrix at `p` defines a bounded operator on `ℓ²(V)`. -/
noncomputable def OperatorBounded (G : BondGraph V E) (p : unitInterval) : Prop := by
  classical
  exact ∃ A : Hilbert V →L[ℂ] Hilbert V, HasKernel G p A

/-- The `ℓ²` threshold `p_{2→2}`. -/
noncomputable def ptwo (G : BondGraph V E) : unitInterval :=
  sSup {p | OperatorBounded G p}

/-- Independent uniform labels on the bonds, for the standard monotone coupling. -/
noncomputable def labelLaw : Measure (E → unitInterval) :=
  Measure.infinitePi (fun _ => (volume : Measure unitInterval))

/-- The bonds open at parameter `p` in the standard monotone coupling. -/
def openEdges (labels : E → unitInterval) (p : unitInterval) : Set E :=
  {e | labels e ≤ p}

/-- Følner's condition: `Λ` is amenable. -/
noncomputable def AmenableGroup (Λ : Type u) [Group Λ] : Prop := by
  classical
  exact ∀ K : Finset Λ, ∀ ε : ℝ, 0 < ε → ∃ A : Finset Λ, A.Nonempty ∧
    ∀ g ∈ K, (((A.image (fun x => x * g)) \ A).card : ℝ) < ε * A.card

/-- The edges `{x, x * s}` of the Cayley graph of `Λ` with respect to `S`. -/
def CayleyEdge {Λ : Type u} [Group Λ] (S : Finset Λ) :=
  {e : Sym2 Λ // ∃ x : Λ, ∃ s ∈ S, e = s(x, x * s)}

/-- The Cayley graph of `Λ` with respect to `S`. -/
def cayleyGraph {Λ : Type u} [Group Λ] (S : Finset Λ) :
    BondGraph Λ (CayleyEdge S) := Subtype.val

/--
**$p_c < p_u$ on nonamenable Cayley graphs**: the Cayley graph of a finitely generated
nonamenable group with respect to a finite symmetric generating set satisfies $p_c < p_u$.

This is the Benjamini–Schramm conjecture [BS96] for Cayley graphs. It was proved by an internal
OpenAI model in September 2026 [OAI26]; see `pc_lt_pu.variants.openai` and OpenAI's Lean
proof.
-/
@[category research solved, AMS 20 60 82]
theorem pc_lt_pu {Λ : Type u} [Group Λ] [Group.FG Λ]
    (hna : ¬ AmenableGroup Λ) (S : Finset Λ)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set Λ) = ⊤)
    (h1 : 1 ∉ S) :
    pc (cayleyGraph S) < pu (cayleyGraph S) := by
  sorry

/--
The statement of OpenAI's Lean proof [OAI26]: the two-point matrix is bounded on $\ell^2$ at
$p_c$, $p_c < p_{2 \to 2} \le p_u$, the standard coupling has infinitely many infinite clusters
simultaneously for all $p$ in some interval, and for every $p \in (p_c, p_u)$ there are almost
surely infinitely many infinite clusters.
-/
@[category research solved, AMS 20 60 82]
theorem pc_lt_pu.variants.openai {Λ : Type u} [Group Λ] [Group.FG Λ]
    (hna : ¬ AmenableGroup Λ) (S : Finset Λ)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set Λ) = ⊤)
    (h1 : 1 ∉ S) :
    OperatorBounded (cayleyGraph S) (pc (cayleyGraph S)) ∧
    pc (cayleyGraph S) < ptwo (cayleyGraph S) ∧
    ptwo (cayleyGraph S) ≤ pu (cayleyGraph S) ∧
    (∃ p₁ p₂ : unitInterval, pc (cayleyGraph S) < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧
      ∀ᵐ labels ∂(labelLaw : Measure (CayleyEdge S → unitInterval)),
        ∀ p ∈ Set.Icc p₁ p₂, (infiniteClusters (cayleyGraph S) (openEdges labels p)).Infinite) ∧
    (∀ p : unitInterval, pc (cayleyGraph S) < p → p < pu (cayleyGraph S) →
      ∀ᵐ ω ∂law p, (infiniteClusters (cayleyGraph S) ω).Infinite) := by
  sorry

/-- OpenAI's Lean statement gives `p_c < p_u`. -/
@[category test, AMS 20 60 82]
theorem pc_lt_pu_of_openai
    (h : type_of% @pc_lt_pu.variants.openai.{u}) : type_of% @pc_lt_pu.{u} := by
  intro Λ _ _ hna S hsym hgen h1
  obtain ⟨-, hlt, hle, -⟩ := h hna S hsym hgen h1
  exact hlt.trans_le hle

end PercolationNonuniqueness
