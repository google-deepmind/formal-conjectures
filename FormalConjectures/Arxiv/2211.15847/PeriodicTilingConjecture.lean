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
# The periodic tiling conjecture

A finite set $F \subseteq \mathbb{Z}^d$ *tiles* $\mathbb{Z}^d$ by translations if there is a set
$A \subseteq \mathbb{Z}^d$ such that every point of $\mathbb{Z}^d$ is uniquely $f + a$ with
$f \in F$ and $a \in A$. The periodic tiling conjecture asserts that every such $F$ also tiles
$\mathbb{Z}^d$ with a translation set $A$ that is invariant under a subgroup of finite index.

*References:*
- [LW96] J. C. Lagarias and Y. Wang, *Tiling the line with translates of one tile*,
  Invent. Math. 124 (1996), 341–365.
- [Ne77] D. J. Newman, *Tesselation of integers*, J. Number Theory 9 (1977), 107–111.
- [Bh20] S. Bhattacharya, *Periodicity and decidability of tilings of $\mathbb{Z}^2$*,
  Amer. J. Math. 142 (2020), 255–266.
- [arxiv/2211.15847](https://arxiv.org/abs/2211.15847)
  **A counterexample to the periodic tiling conjecture**
  by *Rachel Greenfeld and Terence Tao*, Ann. of Math. 200 (2024), 301–363.
- [OAI26] OpenAI, *A translational tile with no fully periodic tiling in dimension three*.
  OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-translational-tile-with-no-fully-periodic-tiling-in-dimension-three-September-23-2026/paper.pdf
-/

@[expose] public section

namespace Arxiv.«2211.15847»

open MeasureTheory

section Lattice

variable {G : Type*} [AddCommGroup G]

/-- `F` tiles `G` with translation set `A`: every element of `G` is uniquely `f + a` with
`f ∈ F` and `a ∈ A`. -/
def Tiles (F : Finset G) (A : Set G) : Prop :=
  Function.Bijective (fun p : ↥F × A => (p.1 : G) + (p.2 : G))

/-- `v` is a period of `A`. -/
def IsPeriod (A : Set G) (v : G) : Prop :=
  ∀ x : G, x + v ∈ A ↔ x ∈ A

/-- `A` is fully periodic: it is invariant under translation by a subgroup of finite index. -/
def FullyPeriodic (A : Set G) : Prop :=
  ∃ P : AddSubgroup G, P.FiniteIndex ∧ ∀ v ∈ P, IsPeriod A v

end Lattice

section Euclidean

variable {d : ℕ}

/-- The union of the unit cubes `z + [0, 1]^d` over `z ∈ F`. -/
def Thickening (F : Finset (Fin d → ℤ)) : Set (Fin d → ℝ) :=
  {x | ∃ z ∈ F, x - (fun i => (z i : ℝ)) ∈ Set.Icc 0 1}

/-- `Ω` tiles `ℝ^d` with translation set `A` up to a null set: almost every `x` is `ω + a` with
`ω ∈ Ω` for exactly one `a ∈ A`. -/
def AETiles (Ω A : Set (Fin d → ℝ)) : Prop :=
  ∀ᵐ x ∂volume, ∃! a : A, x - (a : Fin d → ℝ) ∈ Ω

/-- `A ⊆ ℝ^d` is fully periodic: every vector of some lattice of rank `d` is a period. -/
def EuclideanFullyPeriodic (A : Set (Fin d → ℝ)) : Prop :=
  ∃ b : Module.Basis (Fin d) ℝ (Fin d → ℝ),
    ∀ v ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup, IsPeriod A v

end Euclidean

/--
**The periodic tiling conjecture** [LW96]: if a finite set $F \subseteq \mathbb{Z}^d$ tiles
$\mathbb{Z}^d$ by translations, then it also tiles $\mathbb{Z}^d$ with a fully periodic
translation set.

It is false. Greenfeld and Tao disproved it in a large dimension $d$
[arxiv/2211.15847]. An internal OpenAI model found a counterexample in dimension three in
September 2026 [OAI26]; see `periodic_tiling_conjecture.variants.dim_three` and OpenAI's Lean
proof.
-/
@[category research solved, AMS 5 52]
theorem periodic_tiling_conjecture :
    ¬ ∀ (d : ℕ) (F : Finset (Fin d → ℤ)), (∃ A, Tiles F A) →
      ∃ A, Tiles F A ∧ FullyPeriodic A := by
  sorry

/--
The periodic tiling conjecture fails in $\mathbb{Z}^3$: there is a finite tile of
$\mathbb{Z}^3$ with no fully periodic tiling. Greenfeld and Tao asked whether this holds
[arxiv/2211.15847]; it was proved by an internal OpenAI model in September 2026 [OAI26].
-/
@[category research solved, AMS 5 52]
theorem periodic_tiling_conjecture.variants.dim_three :
    ∃ F : Finset (Fin 3 → ℤ), (∃ A, Tiles F A) ∧ ∀ A, Tiles F A → ¬ FullyPeriodic A := by
  sorry

/--
The periodic tiling conjecture holds in dimensions $d \le 2$: Newman proved it for $d = 1$
[Ne77] and Bhattacharya for $d = 2$ [Bh20]. OpenAI's Lean proof includes both cases, as the
minimality part of its statement.
-/
@[category research solved, AMS 5 52]
theorem periodic_tiling_conjecture.variants.dim_le_two (d : ℕ) (hd : d ≤ 2)
    (F : Finset (Fin d → ℤ)) (hF : ∃ A, Tiles F A) : ∃ A, Tiles F A ∧ FullyPeriodic A := by
  sorry

/--
The Euclidean version fails in $\mathbb{R}^3$: the union of unit cubes over the tile of
`periodic_tiling_conjecture.variants.dim_three` tiles $\mathbb{R}^3$ by translations, up to null
sets, but never with a fully periodic translation set [OAI26].
-/
@[category research solved, AMS 5 52]
theorem periodic_tiling_conjecture.variants.euclidean_dim_three :
    ∃ F : Finset (Fin 3 → ℤ), (∃ A, AETiles (Thickening F) A) ∧
      ∀ A, AETiles (Thickening F) A → ¬ EuclideanFullyPeriodic A := by
  sorry

/--
The statement of OpenAI's Lean proof [OAI26]: a nonempty finite tile of $\mathbb{Z}^3$ with no
fully periodic tiling, whose union of unit cubes tiles $\mathbb{R}^3$ but never periodically,
and $3$ is the least dimension with such a tile.
-/
@[category research solved, AMS 5 52]
theorem periodic_tiling_conjecture.variants.openai :
    (∃ T : Finset (Fin 3 → ℤ), T.Nonempty ∧
      (∃ A : Set (Fin 3 → ℤ), Tiles T A) ∧
      (∀ A : Set (Fin 3 → ℤ), Tiles T A → ¬ FullyPeriodic A) ∧
      (∃ A : Set (Fin 3 → ℝ), AETiles (Thickening T) A) ∧
      (∀ A : Set (Fin 3 → ℝ), AETiles (Thickening T) A → ¬ EuclideanFullyPeriodic A)) ∧
    IsLeast {d : ℕ | ∃ T : Finset (Fin d → ℤ), T.Nonempty ∧ (∃ A, Tiles T A) ∧
      ∀ A, Tiles T A → ¬ FullyPeriodic A} 3 := by
  sorry

/-- A counterexample in dimension three refutes the periodic tiling conjecture. -/
@[category test, AMS 5 52]
theorem periodic_tiling_conjecture_of_dim_three
    (h : type_of% periodic_tiling_conjecture.variants.dim_three) :
    type_of% periodic_tiling_conjecture := by
  intro hall
  obtain ⟨F, hF, hno⟩ := h
  obtain ⟨A, hA, hper⟩ := hall 3 F hF
  exact hno A hA hper

/-- OpenAI's Lean statement gives the counterexample in dimension three. -/
@[category test, AMS 5 52]
theorem periodic_tiling_conjecture.variants.dim_three_of_openai
    (h : type_of% periodic_tiling_conjecture.variants.openai) :
    type_of% periodic_tiling_conjecture.variants.dim_three := by
  obtain ⟨⟨F, -, hF, hno, -⟩, -⟩ := h
  exact ⟨F, hF, hno⟩

/-- OpenAI's Lean statement gives the Euclidean counterexample in dimension three. -/
@[category test, AMS 5 52]
theorem periodic_tiling_conjecture.variants.euclidean_dim_three_of_openai
    (h : type_of% periodic_tiling_conjecture.variants.openai) :
    type_of% periodic_tiling_conjecture.variants.euclidean_dim_three := by
  obtain ⟨⟨F, -, -, -, hF, hno⟩, -⟩ := h
  exact ⟨F, hF, hno⟩

/-- The minimality part of OpenAI's Lean statement gives the cases $d \le 2$. -/
@[category test, AMS 5 52]
theorem periodic_tiling_conjecture.variants.dim_le_two_of_openai
    (h : type_of% periodic_tiling_conjecture.variants.openai) :
    type_of% periodic_tiling_conjecture.variants.dim_le_two := by
  intro d hd F hF
  by_contra hno
  push Not at hno
  obtain ⟨A, hA⟩ := hF
  obtain ⟨⟨f, a⟩, -⟩ := hA.2 0
  have h3 : 3 ≤ d := h.2.2 ⟨F, ⟨f, f.2⟩, ⟨A, hA⟩, hno⟩
  omega

end Arxiv.«2211.15847»
