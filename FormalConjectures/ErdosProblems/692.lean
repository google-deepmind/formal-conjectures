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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 692

*Reference:* [erdosproblems.com/692](https://www.erdosproblems.com/692)

[Er79e] Erdős, P., _Some unconventional problems in number theory_ (1979).

[Ob1] Oberwolfach problem session (1986).

[Ca25] Cambie, S., disproved the conjecture by exhibiting non-unimodality for $n = 3$.
-/

open Finset Filter

namespace Erdos692

/-- The number of divisors of $k$ that lie strictly between $n$ and $m$. -/
def countDivisorsInOpenInterval (k n m : ℕ) : ℕ :=
  ((Nat.divisors k).filter (fun d => n < d ∧ d < m)).card

/-- The proportion of positive integers up to $N$ having exactly one divisor
in the open interval $(n, m)$. This approximates $\delta_1(n, m)$. -/
noncomputable def delta1Approx (n m N : ℕ) : ℝ :=
  (((Finset.range (N + 1)).filter
    (fun k => 0 < k ∧ countDivisorsInOpenInterval k n m = 1)).card : ℝ) / (N : ℝ)

/-- The natural density $\delta_1(n, m)$ exists and equals $d$:
the limit of $|\{k \leq N : k \text{ has exactly one divisor in } (n, m)\}| / N$ equals $d$. -/
def HasDelta1Density (n m : ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N => delta1Approx n m N) Filter.atTop (nhds d)

/--
Erdős Problem 692 [Er79e, Ob1] — DISPROVED

Let $\delta_1(n, m)$ be the natural density of the set of positive integers with exactly
one divisor in the open interval $(n, m)$. Erdős asked (1986, Oberwolfach) whether,
for fixed $n$, $\delta_1(n, m)$ is unimodal as a function of $m$ for $m > n + 1$.

Cambie [Ca25] disproved this by showing it fails even for $n = 3$:
$$\delta_1(3, 6) = 0.35, \quad \delta_1(3, 7) \approx 0.33, \quad \delta_1(3, 8) \approx 0.3619,$$
exhibiting a "valley" at $m = 7$ that contradicts unimodality.
Furthermore, for fixed $n$, the sequence $\delta_1(n, m)$ has superpolynomially many
local maxima in $m$.

The RHS formalizes unimodality: for every $n$ and $m_1 < m_2 < m_3$ (all $> n + 1$),
the density at $m_2$ is not a strict local minimum (i.e., $d_1 \le d_2$ or $d_3 \le d_2$).
The answer is `False` because Cambie exhibited a counterexample.
-/
@[category research solved, AMS 11]
theorem erdos_692 : answer(False) ↔
    ∀ n : ℕ, ∀ m₁ m₂ m₃ : ℕ,
      n + 1 < m₁ → m₁ < m₂ → m₂ < m₃ →
      ∀ d₁ d₂ d₃ : ℝ,
        HasDelta1Density n m₁ d₁ →
        HasDelta1Density n m₂ d₂ →
        HasDelta1Density n m₃ d₃ →
        d₁ ≤ d₂ ∨ d₃ ≤ d₂ := by
  sorry

end Erdos692
