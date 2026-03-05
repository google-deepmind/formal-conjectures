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
# Erdős Problem 962

*Reference:* [erdosproblems.com/962](https://www.erdosproblems.com/962)

Let $k(n)$ be the maximal $k$ such that there exists $m \leq n$ such that each
of the integers $m+1, \ldots, m+k$ are divisible by at least one prime $> k$.
Estimate $k(n)$.

[Er65] Erdős, P., _Extremal problems in number theory_, 1965.
-/

open Real

namespace Erdos962

/--
`erdos962_k n` is the maximal $k$ such that there exists $m \leq n$ with every
integer in $\{m+1, \ldots, m+k\}$ divisible by at least one prime greater than $k$.
-/
noncomputable def erdos962_k (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ m : ℕ, m ≤ n ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ k → ∃ p : ℕ, Nat.Prime p ∧ p > k ∧ p ∣ (m + i)}

/--
Erdős Problem 962, conjecture [Er65]:

$k(n) = o(n^\epsilon)$ for every $\epsilon > 0$. That is, for every $\epsilon > 0$,
$k(n) / n^\epsilon \to 0$ as $n \to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_962 (ε : ℝ) (hε : ε > 0) :
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos962_k n : ℝ) ≤ δ * (n : ℝ) ^ ε := by
  sorry

/--
Erdős Problem 962, Tao's upper bound:

$k(n) \leq (1+o(1)) n^{1/2}$. Formulated as: for every $\epsilon > 0$, there
exists $N_0$ such that for all $n \geq N_0$, $k(n) \leq (1+\epsilon) \sqrt{n}$.
-/
@[category research solved, AMS 11]
theorem erdos_962.variants.tao_upper (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos962_k n : ℝ) ≤ (1 + ε) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/--
Erdős Problem 962, Erdős lower bound [Er65]:

$k(n) \gg_\epsilon \exp((\log n)^{1/2-\epsilon})$ for every $\epsilon > 0$.
Formulated as: for every $\epsilon > 0$, there exist $C > 0$ and $N_0$ such that
for all $n \geq N_0$, $k(n) \geq C \cdot \exp((\log n)^{1/2-\epsilon})$.
-/
@[category research solved, AMS 11]
theorem erdos_962.variants.erdos_lower (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos962_k n : ℝ) ≥ C * exp ((log (n : ℝ)) ^ ((1 : ℝ) / 2 - ε)) := by
  sorry

/--
Erdős Problem 962, Tang's lower bound:

$k(n) \geq \exp((1/\sqrt{2} - o(1))\sqrt{\log n \cdot \log\log n})$.
Formulated as: for every $\epsilon > 0$, there exists $N_0$ such that for all
$n \geq N_0$, $k(n) \geq \exp((1/\sqrt{2} - \epsilon) \cdot \sqrt{\log n \cdot \log(\log n)})$.
-/
@[category research solved, AMS 11]
theorem erdos_962.variants.tang_lower (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos962_k n : ℝ) ≥
        exp ((1 / sqrt 2 - ε) * sqrt (log (n : ℝ) * log (log (n : ℝ)))) := by
  sorry

end Erdos962
