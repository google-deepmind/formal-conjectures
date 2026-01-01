/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1095

*Reference:* [erdosproblems.com/1095](https://www.erdosproblems.com/1095)
-/

open Nat hiding log
open Real Filter
open scoped Asymptotics Topology

namespace Erdos1095

/--
Let $g(k)>k+1$ be maximal such that
if $n\leq g(k)$ then $\binom{n}{k}$ is divisible by a prime $\leq k$.
Estimate $g(k)$.
-/
noncomputable def g (k : ℕ) : ℕ :=
  sSup {m | ∀ n ∈ Set.Ioc k m, ∃ p ≤ k, p.Prime ∧ p ∣ choose n k}

/--
The current record is\[g(k) \gg \exp(c(\log k)^2)\]for some $c>0$, due to Konyagin
[Ko99b](https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/S0025579300007555).
-/
@[category research solved, AMS 11]
theorem erdos_1095_lower_solved :
    ∃ c > 0, (fun k : ℕ ↦ exp (c * log k ^ 2)) =O[atTop] fun k ↦ (g k : ℝ) := by
  sorry

/--
Ecklund, Erdős, and Selfridge conjectured $g(k)\leq \exp(k^{1+o(1)})$
[EES74](https://mathscinet.ams.org/mathscinet/relay-station?mr=1199990)
-/
@[category research open, AMS 11]
theorem erdos_1095_upper_conjecture :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ k, g k ≤ exp (k ^ (1 + f k)) := by
  sorry

/--
Erdős, Lacampagne, and Selfridge [ELS93](https://www.ams.org/journals/mcom/1993-61-203/S0025-5718-1993-1199990-6/S0025-5718-1993-1199990-6.pdf)
write 'it is clear to every right-thinking person' that
$g(k)\geq\exp(c\frac{k}{\log k})$ for some constant $c>0$.
-/
@[category research open, AMS 11]
theorem erdos_1095_lower_conjecture : ∃ c > 0, ∀ k, g k ≥ exp (c * k / log k) :=
  sorry

/--
[Sorenson, Sorenson, and Webster](https://mathscinet.ams.org/mathscinet/relay-station?mr=4235124)
give heuristic evidence that \[\log g(k) \asymp \frac{k}{\log k}.\]
-/
@[category research open, AMS 11]
theorem erdos_1095_log_equivalent : (fun k ↦ log (g k)) ~[atTop] (fun k ↦ k / log k) :=
  sorry

end Erdos1095
