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
# Mauras's conjectures on stable pairs and individual stable partners

*Reference:* S. Mauras,
[Analysis of Random Models for Stable Matchings](https://www.irif.fr/~mauras/thesis/thesis.pdf),
PhD dissertation, Université de Paris (2021), Section 5.8, pp. 63–64.

The first conjecture concerns uniformly reassigning the lists on both sides of a fixed market.
The second bounds each named agent's expected number of stable partners under aligned popularity
preferences. We state the balanced case with complete strict lists and positive popularity weights.
-/

@[expose] public section

open scoped NNReal

namespace MaurasStablePairs

/-- Independent complete rankings using a public popularity weight for each person. -/
noncomputable def popularityProfile {n : ℕ} (a b : Fin n → ℝ≥0) :
    PMF (StableMarriage.Profile n) :=
  RandomRanking.profile (fun _ w ↦ a w) (fun m _ ↦ b m)

/-- Expected number of different stable partners of a specified man. -/
noncomputable def expectedManStablePartners {n : ℕ} (a b : Fin n → ℝ≥0) (m : Fin n) : ℝ :=
  ∫ p, ((StableMarriage.manStablePartners p m).card : ℝ) ∂(popularityProfile a b).toMeasure

/-- Expected number of different stable partners of a specified woman. -/
noncomputable def expectedWomanStablePartners {n : ℕ} (a b : Fin n → ℝ≥0) (w : Fin n) : ℝ :=
  ∫ p, ((StableMarriage.womanStablePartners p w).card : ℝ) ∂(popularityProfile a b).toMeasure

/-- A singleton man has exactly one stable partner under every popularity distribution. -/
@[category test, AMS 5 60 91]
theorem expectedManStablePartners_one (a b : Fin 1 → ℝ≥0) :
    expectedManStablePartners a b 0 = 1 := by
  simp [expectedManStablePartners]

/-- A singleton woman has exactly one stable partner under every popularity distribution. -/
@[category test, AMS 5 60 91]
theorem expectedWomanStablePartners_one (a b : Fin 1 → ℝ≥0) :
    expectedWomanStablePartners a b 0 = 1 := by
  simp [expectedWomanStablePartners]

/--
For any complete strict profile on $n$ people per side, independently and uniformly reassigning
both sides' lists gives at most $n(1+\log n)$ distinct stable pairs in expectation.
This is the shuffling conjecture in Section 5.8, p. 64.
-/
@[category research open, AMS 5 60 91]
theorem shuffled_stable_pairs_bound (n : ℕ) (hn : 0 < n) (p : StableMarriage.Profile n) :
    StableMarriage.expectedNumStablePairsAfterShuffle p ≤ n * (1 + Real.log n) := by
  sorry

/--
With aligned positive popularity weights on both sides, each named man has at most
$1+\log n$ different stable partners in expectation. This is the individual-partner conjecture
in Section 5.8, p. 63, specialized to complete balanced markets.
-/
@[category research open, AMS 5 60 91]
theorem individual_man_stable_partners_bound (n : ℕ) (hn : 0 < n)
    (a b : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (m : Fin n) :
    expectedManStablePartners a b m ≤ 1 + Real.log n := by
  sorry

/--
With aligned positive popularity weights on both sides, each named woman has at most
$1+\log n$ different stable partners in expectation. This is the other side of the
individual-partner conjecture in Section 5.8, p. 63, for complete balanced markets.
-/
@[category research open, AMS 5 60 91]
theorem individual_woman_stable_partners_bound (n : ℕ) (hn : 0 < n)
    (a b : Fin n → ℝ≥0) (ha : ∀ w, 0 < a w) (hb : ∀ m, 0 < b m) (w : Fin n) :
    expectedWomanStablePartners a b w ≤ 1 + Real.log n := by
  sorry

end MaurasStablePairs
