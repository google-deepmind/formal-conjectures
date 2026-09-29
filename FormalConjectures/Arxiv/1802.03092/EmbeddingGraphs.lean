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
# Spherical representations of graphs of bounded degree

N. Frankl, A. Kupavskii and K. J. Swanepoel, *Embedding graphs in Euclidean space*,
J. Combin. Theory Ser. A 171 (2020), 105146, §5, Problem 1.

*Reference:* [arxiv/1802.03092](https://arxiv.org/abs/1802.03092)
-/

@[expose] public section

namespace Arxiv.«1802.03092»

/-- A graph has spherical dimension at most $d$ if it admits an injective placement in
$\mathbb{R}^d$ on the sphere of radius $1/\sqrt{2}$ centred at the origin, with every edge
of length $1$. Non-adjacent vertices may also be at distance $1$. -/
def HasSphericalDimAtMost (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective f ∧
    (∀ v, ‖f v‖ = 1 / √2) ∧ ∀ u v, G.Adj u v → dist (f u) (f v) = 1

/-- Some connected component is isomorphic to $K_{d+1}$: its reachability class has
$d+1$ vertices, and any two distinct vertices in that class are adjacent. -/
def HasCompleteComponent (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ v : Fin n, Nonempty ({w : Fin n // G.Reachable v w} ≃ Fin (d + 1)) ∧
    ∀ a b, G.Reachable v a → G.Reachable v b → a ≠ b → G.Adj a b

/-- Forgetting the sphere gives a unit-distance representation. -/
@[category test, AMS 5 52]
theorem unitDistanceEmbeddable_of_hasSphericalDimAtMost {d n : ℕ}
    {G : SimpleGraph (Fin n)} (h : HasSphericalDimAtMost d G) :
    G.UnitDistanceEmbeddable d := by
  obtain ⟨f, hf, _, hdist⟩ := h
  exact ⟨f, hf, hdist⟩

/-- The graph with no vertices admits an empty placement in every dimension. -/
@[category test, AMS 5 52]
theorem hasSphericalDimAtMost_empty (d : ℕ) (G : SimpleGraph (Fin 0)) :
    HasSphericalDimAtMost d G := by
  exact ⟨Fin.elim0, Function.injective_of_subsingleton _, by simp, by simp⟩

/-- The graph with no vertices has no complete component. -/
@[category test, AMS 5]
theorem not_hasCompleteComponent_empty (d : ℕ) (G : SimpleGraph (Fin 0)) :
    ¬ HasCompleteComponent d G := by
  simp [HasCompleteComponent]

/-- The complete graph $K_{d+1}$ has a complete component of the excluded size. -/
@[category test, AMS 5]
theorem hasCompleteComponent_completeGraph (d : ℕ) :
    HasCompleteComponent d (SimpleGraph.completeGraph (Fin (d + 1))) := by
  refine ⟨0, ⟨Equiv.subtypeUnivEquiv (fun _ => SimpleGraph.reachable_top)⟩, ?_⟩
  exact fun _ _ _ _ hab => hab

/-- The complete graph $K_{d+1}$ has no spherical representation in $\mathbb{R}^d$. -/
@[category test, AMS 5 52]
theorem not_hasSphericalDimAtMost_completeGraph (d : ℕ) :
    ¬ HasSphericalDimAtMost d (SimpleGraph.completeGraph (Fin (d + 1))) := by
  rintro ⟨f, _, hnorm, hdist⟩
  have hr : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hne : ∀ i, f i ≠ 0 := by
    intro i hi
    have := hnorm i
    rw [hi, norm_zero] at this
    have : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
    linarith
  have horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0 := by
    intro i j hij
    have hd := hdist i j hij
    rw [dist_eq_norm] at hd
    have hs := norm_sub_sq_real (f i) (f j)
    rw [hd, hnorm i, hnorm j, hr] at hs
    linarith
  have hcard := (linearIndependent_of_ne_zero_of_inner_eq_zero hne horth).fintype_card_le_finrank
  simp only [finrank_euclideanSpace_fin, Fintype.card_fin] at hcard
  omega

open scoped Classical in
/-- **Problem 1.** For every $d>3$, does every finite graph of maximum degree at most $d$
with no connected component isomorphic to $K_{d+1}$ have a spherical representation in
$\mathbb{R}^d$?

The exception is read componentwise. Excluding only the graph $K_{d+1}$ would leave the
counterexample $K_{d+1} \sqcup K_1$. The paper also uses a componentwise exception in the
preceding discussion of its Euclidean result. "Maximum degree $d$" is read as at most $d$;
Proposition 2 already covers smaller maximum degrees. -/
@[category research open, AMS 5 52]
theorem problem_1 :
    answer(sorry) ↔ ∀ d : ℕ, 3 < d → ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.maxDegree ≤ d → ¬ HasCompleteComponent d G → HasSphericalDimAtMost d G := by
  sorry

open scoped Classical in
/-- The $d=4$ instance of Problem 1: does every finite graph of maximum degree at most $4$
with no connected component isomorphic to $K_5$ have a spherical representation in
$\mathbb{R}^4$? -/
@[category research open, AMS 5 52]
theorem problem_1.variants.dimension_four :
    answer(sorry) ↔ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.maxDegree ≤ 4 → ¬ HasCompleteComponent 4 G → HasSphericalDimAtMost 4 G := by
  sorry

end Arxiv.«1802.03092»
