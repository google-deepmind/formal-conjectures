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
# Always-matched workers under switching costs

In §3 of [Stable matchings under relaxed random preferences](https://doi.org/10.1007/s00182-026-01016-x),
Boris Pittel and Kirill Rudov ask how the expected number of workers matched in every stable
matching changes with the switching cost. Figure 3(d) of their
[working paper](https://krudov.com/papers/JMP_Kirill_Rudov.pdf#page=24) measures this fraction in
finite markets. The question below specifies one extra worker and asks for a fixed fractional drop
at a vanishing supercritical cost.
-/

@[expose] public section

open Filter MeasureTheory SwitchingCostMatching

namespace AlwaysMatchedWorkers

/-- The utility profiles in which worker $j$ is matched in every matching stable at cost
$\varepsilon$. -/
def alwaysMatchedEvent (n : ℕ) (ε : ℝ) (j : Fin (n + 1)) : Set (Profile n) :=
  {p | ∀ m : Matching n, IsStable p ε m → j ∈ Set.range m}

/-- Whether a given worker is matched in every stable matching is a measurable event. -/
@[category API, AMS 60]
theorem measurableSet_alwaysMatchedEvent (n : ℕ) (ε : ℝ) (j : Fin (n + 1)) :
    MeasurableSet (alwaysMatchedEvent n ε j) := by
  apply Measurable.setOf
  unfold IsStable IsBlockingPair
  fun_prop (disch := exact measurable_pi_apply _)

/-- The expected number of workers matched in every stable matching is the sum of the
probabilities of the individual workers' events. -/
noncomputable def expectedAlwaysMatched (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), (profileMeasure n).real (alwaysMatchedEvent n ε j)

/-- Increasing the cost expands the stable set, so the expected count is nonincreasing. -/
@[category API, AMS 5 60]
theorem expectedAlwaysMatched_antitone (n : ℕ) : Antitone (expectedAlwaysMatched n) := by
  intro ε ε' h
  refine Finset.sum_le_sum fun j _ ↦ measureReal_mono ?_
  intro p hp m hm
  exact hp m (hm.mono h)

/-- In a market with $n$ firms and $n+1$ workers and independent rate-one exponential utilities,
let $C_n$ count the workers matched in every matching stable at cost
$\varepsilon_n = \log n/(6\sqrt n)$. Is $\mathbb{E}[C_n]$ eventually at most $(1-c)n$ for some
constant $c \in (0,1)$? The limit uses positive market sizes $n = k+1$. -/
@[category research open, question, AMS 5 60]
theorem alwaysMatchedWorkers :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ᶠ k : ℕ in atTop,
      let n := k + 1
      expectedAlwaysMatched n (Real.log n / (6 * Real.sqrt n)) ≤ (1 - c) * (n : ℝ) := by
  sorry

end AlwaysMatchedWorkers
