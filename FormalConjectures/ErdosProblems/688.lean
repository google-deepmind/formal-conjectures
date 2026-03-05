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
# Erdős Problem 688

*Reference:* [erdosproblems.com/688](https://www.erdosproblems.com/688)

Define $\varepsilon_n$ to be maximal such that there exists some choice of congruence
class $a_p$ for all primes $n^{\varepsilon_n} < p \leq n$ such that every integer in $[1, n]$
satisfies at least one of the congruences $\equiv a_p \pmod{p}$.

Estimate $\varepsilon_n$ — in particular is it true that $\varepsilon_n = o(1)$?

Erdős could prove $\varepsilon_n \gg (\log \log \log n) / (\log \log n)$.

See also problems [#687](https://www.erdosproblems.com/687) and
[#689](https://www.erdosproblems.com/689).
-/

namespace Erdos688

/-- A choice of residue classes for primes $p$ in $(n^\varepsilon, n]$ covers $[1, n]$ if
every integer $m \in \{1, \ldots, n\}$ satisfies $m \equiv a(p) \pmod{p}$ for some
prime $p$ with $n^\varepsilon < p \leq n$. -/
def PrimeCoveringInRange (n : ℕ) (ε : ℝ) (a : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n →
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ ε < (p : ℝ) ∧ p ≤ n ∧ m % p = a p % p

/-- Erdős Problem 688 (conjecture): $\varepsilon_n = o(1)$.
For any fixed $\delta > 0$, for sufficiently large $n$, the primes in $(n^\delta, n]$
cannot cover $[1, n]$ with any choice of congruence classes. -/
@[category research open, AMS 11]
theorem erdos_688 : answer(sorry) ↔
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ¬∃ a : ℕ → ℕ, PrimeCoveringInRange n δ a := by
  sorry

/-- Known lower bound: $\varepsilon_n \gg (\log \log \log n) / (\log \log n)$.
For some constant $C > 0$, for all sufficiently large $n$, there exists a
covering using primes in $(n^{C \cdot \log\log\log(n)/\log\log(n)}, n]$. -/
@[category research solved, AMS 11]
theorem erdos_688.variants.lower_bound :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ a : ℕ → ℕ, PrimeCoveringInRange n
        (C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ))) a := by
  sorry

end Erdos688
