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
# Erdős Problem 841

*Reference:* [erdosproblems.com/841](https://www.erdosproblems.com/841)

Let $t_n$ be minimal such that $\{n+1, \ldots, n+t_n\}$ contains a subset whose
product with $n$ is a square number (and let $t_n = 0$ if $n$ is itself square).
Estimate $t_n$.

A problem of Erdős, Graham, and Selfridge.

[ErSe92] Erdős, P. and Selfridge, J. L., 1992.

[BPZ24] Bui, H. M., Pratt, K., and Zaharescu, A., 2024.
-/

open Finset

namespace Erdos841

/-- The set $\{n+1, \ldots, n+t\}$ contains a nonempty subset whose product with $n$
is a perfect square. -/
def HasSquareProductSubset (n t : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ Finset.Icc (n + 1) (n + t) ∧
    IsSquare (n * S.prod id)

/-- $t_n$: the minimal $t$ such that $\{n+1, \ldots, n+t\}$ contains a nonempty subset whose
product with $n$ is a perfect square. Defined as $0$ when $n$ is a perfect square. -/
noncomputable def erdos841T (n : ℕ) : ℕ :=
  if IsSquare n then 0
  else sInf {t : ℕ | HasSquareProductSubset n t}

/-- The largest prime factor of $n$, or $0$ if $n \leq 1$. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  (Nat.primeFactors n).sup id

/--
**Erdős Problem 841** — Trivial lower bound:

For all non-square $n \geq 2$, $t_n \geq P(n)$ where $P(n)$ is the largest prime factor of $n$.
-/
@[category undergraduate, AMS 11]
theorem erdos_841 (n : ℕ) (hn : n ≥ 2) (hns : ¬IsSquare n) :
    erdos841T n ≥ largestPrimeFactor n := by
  sorry

/--
**Erdős Problem 841** — Selfridge's result [ErSe92]:

If the largest prime factor $P(n) > \sqrt{2n} + 1$, then $t_n = P(n)$.
-/
@[category research solved, AMS 11]
theorem erdos_841.variants.selfridge (n : ℕ) (hn : n ≥ 2) (hns : ¬IsSquare n)
    (hP : (largestPrimeFactor n : ℝ) > Real.sqrt (2 * (n : ℝ)) + 1) :
    erdos841T n = largestPrimeFactor n := by
  sorry

/--
**Erdős Problem 841** — Selfridge's upper bound [ErSe92]:

If $P(n) \leq \sqrt{2n} + 1$, then $t_n \ll \sqrt{n}$. Formally: there exists $C > 0$ such that
for all non-square $n \geq 2$ with $P(n) \leq \sqrt{2n} + 1$, we have $t_n \leq C \cdot \sqrt{n}$.
-/
@[category research solved, AMS 11]
theorem erdos_841.variants.selfridge_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 → ¬IsSquare n →
    (largestPrimeFactor n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) + 1 →
    (erdos841T n : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
  sorry

/--
**Erdős Problem 841** — Bui–Pratt–Zaharescu lower bound [BPZ24]:

For all non-square $n \geq N_0$,
$$t_n \geq C \cdot (\log \log n)^{6/5} \cdot (\log \log \log n)^{-1/5}.$$
-/
@[category research solved, AMS 11]
theorem erdos_841.variants.bpz_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ¬IsSquare n →
    (erdos841T n : ℝ) ≥
      C * (Real.log (Real.log (n : ℝ))) ^ ((6 : ℝ) / 5) *
        (Real.log (Real.log (Real.log (n : ℝ)))) ^ (-(1 : ℝ) / 5) := by
  sorry

end Erdos841
