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
# Erdős Problem 698

*Reference:* [erdosproblems.com/698](https://www.erdosproblems.com/698)

A problem of Erdős and Szekeres [ErSz78], who observed that
$$\gcd\left(\binom{n}{i}, \binom{n}{j}\right) \geq \frac{\binom{n}{i}}{\binom{j}{i}} \geq 2^i$$
(in particular the greatest common divisor is always $> 1$). This inequality is
sharp for $i = 1$, $j = p$, and $n = 2p$.

Resolved by Bergman [Be11], who proved that for any $2 \leq i < j \leq n/2$,
$$\gcd\left(\binom{n}{i}, \binom{n}{j}\right) \gg n^{1/2} \cdot 2^i / i^{3/2},$$
where the implied constant is absolute.
-/

open Filter

namespace Erdos698

/--
Erdős Problem 698 [ErSz78] — proved by Bergman [Be11]:
There exists $h : \mathbb{N} \to \mathbb{N}$ with $h(n) \to \infty$ such that for all
$2 \leq i < j \leq n/2$,
$$\gcd\left(\binom{n}{i}, \binom{n}{j}\right) \geq h(n).$$
-/
@[category research solved, AMS 5 11]
theorem erdos_698 : answer(True) ↔
    ∃ h : ℕ → ℕ, Tendsto h atTop atTop ∧
    ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
      h n ≤ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by
  sorry

end Erdos698
