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

This conjecture is false: for every integer $N \ge 13$ (both even and odd),
every complete strict preference profile on $N$ agents admits a $(\lceil N/2\rceil - 1)$-stable
matching, so $K(N) = \lceil N/2\rceil - 1 < \lceil N/2\rceil$.
-/
@[category research solved, AMS 5 68 91, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000033&version=1"]
theorem stability_threshold_tight :
    ¬ (∃ N₀ : ℕ, 3 ≤ N₀ ∧
      ∀ N ≥ N₀, Roommates.stabilityThreshold N = (N + 1) / 2) := by
  sorry

/--
For every integer $N \ge 13$ (both even $N = 2m \ge 14$ and odd $N = 2m - 1 \ge 13$),
the exact universal rank-improvement stability threshold is $K(N) = \lceil N / 2 \rceil - 1$.
-/
@[category research solved, AMS 5 68 91, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-28-000033&version=1"]
theorem stability_threshold_exact_ge_13 :
    ∀ N : ℕ, 13 ≤ N → Roommates.stabilityThreshold N = (N + 1) / 2 - 1 := by
  sorry

end FanelliMoscardelli
