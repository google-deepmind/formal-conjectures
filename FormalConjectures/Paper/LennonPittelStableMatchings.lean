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
# Lennon–Pittel conjecture on random stable matchings

*References:*
- [On the Likely Number of Stable Marriages](https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1194991095&disposition=inline)
  by *Craig Lennon*, PhD dissertation, The Ohio State University (2007).
- [On the Likely Number of Solutions for the Stable Marriage Problem](https://doi.org/10.1017/S0963548308009607)
  by *Craig Lennon and Boris Pittel*, *Combinatorics, Probability and Computing* 18 (2009),
  371–421.

Let $S_n$ be the number of stable matchings under uniformly random complete strict preferences.
-/

open Filter
open scoped Topology

namespace LennonPittel

/-- Sanity check: the uniform profile distribution has total mass one. -/
@[category test, AMS 5 60]
theorem uniform_profile_univ (n : ℕ) :
    (StableMarriage.uniformProfile n).toMeasure Set.univ = 1 := by
  simp

/--
The [Lennon–Pittel conjecture](https://doi.org/10.1017/S0963548308009607) states that for every
positive nonincreasing sequence $\varepsilon_n \to 0$, the probability that the number $S_n$ of
stable matchings is at least $\varepsilon_n \mathbb{E}[S_n]$ tends to one.
-/
@[category research open, AMS 5 60]
theorem lennon_pittel_conjecture
    (ε : ℕ → ℝ) (hε_pos : ∀ n, 0 < ε n) (hε_antitone : Antitone ε)
    (hε_tendsto : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun n ↦
        (StableMarriage.uniformProfile n).toMeasure
          {p | (StableMarriage.numStableMatchings p : ℝ) ≥
            ε n * StableMarriage.expectedNumStableMatchings n})
      atTop (𝓝 1) := by
  sorry

end LennonPittel
