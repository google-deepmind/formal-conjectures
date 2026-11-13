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
# Concentration of match types in tiered random markets

*Reference:* I. Ashlagi, M. Braverman, A. Saberi, C. Thomas and G. Zhao,
[Tiered Random Matching Markets:
Rank Is Proportional to Popularity](https://arxiv.org/abs/2009.05124v2),
full version, Appendix H, Remark H.1 (2021).
The conference version appeared at [ITCS 2021](https://doi.org/10.4230/LIPIcs.ITCS.2021.46).

There are fixed finite numbers of tiers on each side, fixed positive population shares, and
fixed positive public scores. Rankings are independent weighted draws without replacement.
As in Definition 2.2, footnote 5, tier sizes may be rounded to integers with error at most one.
-/

@[expose] public section

open Filter
open scoped Topology NNReal

namespace Arxiv.«2009.05124»

/-- Number of couples between women's tier $i$ and men's tier $j$ under men-proposing DA. -/
noncomputable def matchCount {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (i : Fin I) (j : Fin J)
    (p : StableMarriage.Profile n) : ℕ := by
  classical
  exact (Finset.univ.filter fun w ↦ womanTier w = i ∧
    ∃ m, (StableMarriage.deferredAcceptance p).held w = some m ∧ manTier m = j).card

/-- Independent rankings sampled proportionally to the public scores of the opposite side. -/
noncomputable def market {n I J : ℕ} (womanTier : Fin n → Fin I)
    (manTier : Fin n → Fin J) (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0) :
    PMF (StableMarriage.Profile n) :=
  RandomRanking.profile (fun _ w ↦ α (womanTier w)) (fun m _ ↦ β (manTier m))

/-- An empty market has no matches between any tiers. -/
@[category test, AMS 5 60 91]
theorem matchCount_zero {I J : ℕ} (womanTier : Fin 0 → Fin I) (manTier : Fin 0 → Fin J)
    (i : Fin I) (j : Fin J) (p : StableMarriage.Profile 0) :
    matchCount womanTier manTier i j p = 0 := by
  simp [matchCount]

/-- A singleton market with one tier on each side has one match between those tiers. -/
@[category test, AMS 5 60 91]
theorem matchCount_one (p : StableMarriage.Profile 1) :
    matchCount (fun _ ↦ (0 : Fin 1)) (fun _ ↦ (0 : Fin 1)) 0 0 p = 1 := by
  have hp : p = default := by
    cases p
    congr <;> exact Subsingleton.elim _ _
  subst p
  have h : (StableMarriage.deferredAcceptance (default : StableMarriage.Profile 1)).held 0 =
      some 0 := by decide
  simp [matchCount, Finset.univ_unique, Finset.filter_singleton, h]

/--
Remark H.1 conjectures concentration of the realized table of match types:
$X_{ij}/n \to a_i b_j$ in probability. All scores and shares remain fixed as $n$ grows.
-/
@[category research open, AMS 5 60 91]
theorem match_type_concentration
    (I J : ℕ) (a : Fin I → ℝ) (b : Fin J → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (ha_sum : ∑ i, a i = 1) (hb_sum : ∑ j, b j = 1)
    (α : Fin I → ℝ≥0) (β : Fin J → ℝ≥0)
    (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j)
    (womanTier : (n : ℕ) → Fin n → Fin I) (manTier : (n : ℕ) → Fin n → Fin J)
    (hw : ∀ n i, |(Fintype.card {w // womanTier n w = i} : ℝ) - n * a i| ≤ 1)
    (hm : ∀ n j, |(Fintype.card {m // manTier n m = j} : ℝ) - n * b j| ≤ 1)
    (i : Fin I) (j : Fin J) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (market (womanTier n) (manTier n) α β).toMeasure
      {p | |(matchCount (womanTier n) (manTier n) i j p : ℝ) / n - a i * b j| ≤ ε})
      atTop (𝓝 1) := by
  sorry

end Arxiv.«2009.05124»
