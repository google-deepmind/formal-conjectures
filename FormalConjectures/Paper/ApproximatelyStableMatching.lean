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
# Fanelli–Moscardelli conjecture on approximate roommates stability

*Reference:* A. Fanelli and L. Moscardelli,
[Approximately Stable Matching](https://doi.org/10.3233/FAIA251234), Section 5.

For complete strict preferences on $N$ agents, let $K(N)$ be the least positive rank-improvement
threshold that guarantees a stable matching for every profile. A pair blocks at threshold $k$
when both agents gain at least $k$ positions. Singles have rank $N$.
-/

@[expose] public section

namespace FanelliMoscardelli

/--
The universal rank-improvement threshold is $K(N)=\lceil N/2\rceil$ for every sufficiently
large number of agents.
-/
@[category research open, AMS 5 68 91]
theorem stability_threshold_tight :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ N ≥ N₀, Roommates.stabilityThreshold N = (N + 1) / 2 := by
  sorry

end FanelliMoscardelli
