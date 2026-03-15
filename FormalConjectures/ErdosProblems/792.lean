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
import FormalConjecturesForMathlib.Combinatorics.Basic

/-!
# Erdős Problem 792

*Reference:* [erdosproblems.com/792](https://www.erdosproblems.com/792)

Let $f(n)$ be maximal such that in any $A \subset \mathbb{Z}$ with $|A| = n$ there exists some
sum-free subset $B \subseteq A$ with $|B| \geq f(n)$, so that there are no solutions to
$a + b = c$ with $a, b, c \in B$. Estimate $f(n)$.

Erdős [Er65] gave a simple proof that $f(n) \geq n/3$. Alon and Kleitman [AlKl90] improved this
to $f(n) \geq (n+1)/3$, and Bourgain [Bo97] further improved it to $f(n) \geq (n+2)/3$. The best
lower bound known is $f(n) \geq n/3 + c \log \log n$ for some $c > 0$, due to Bedert [Be25b].
The best upper bound known is $f(n) \leq n/3 + o(n)$, due to Eberhard, Green, and
Manners [EGM14].

This is listed as Problem 1 on Ben Green's open problems list.

[Er65] Erdős, P., *Extremal problems in number theory*. Proc. Sympos. Pure Math.,
Vol. VIII (1965), 181-189.

[AlKl90] Alon, N., Kleitman, D. J., *Sum-free subsets*. (1990), 13-26.

[Bo97] Bourgain, J., *Estimates related to sumfree subsets of sets of integers*. Israel J.
Math. (1997), 71-92.

[Be25b] Bedert, B., *Large sum-free subsets of sets of integers via L¹-estimates for
trigonometric sums*. arXiv:2502.08624 (2025).

[EGM14] Eberhard, S., Green, B., Manners, F., *Sets of integers with no large
sum-free subset*. Ann. of Math. (2) 180 (2014), 621-652.
-/

open scoped Pointwise

namespace Erdos792

/-- $f(n)$ is the largest $k$ such that every $n$-element subset of $\mathbb{Z}$ contains
a sum-free subset of size at least $k$. -/
noncomputable def maxSumFreeSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ (A : Finset ℤ), A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ IsSumFree (B : Set ℤ) ∧ k ≤ B.card}

/--
Erdős Problem 792, Erdős's lower bound [Er65]:
$f(n) \geq n/3$ for all $n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_792 (n : ℕ) :
    (maxSumFreeSize n : ℝ) ≥ n / 3 := by
  sorry

/--
Erdős Problem 792, Alon–Kleitman lower bound [AlKl90]:
$f(n) \geq (n+1)/3$ for all $n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_792.variants.lower_alon_kleitman (n : ℕ) :
    (maxSumFreeSize n : ℝ) ≥ (n + 1) / 3 := by
  sorry

/--
Erdős Problem 792, Bourgain lower bound [Bo97]:
$f(n) \geq (n+2)/3$ for all $n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_792.variants.lower_bourgain (n : ℕ) :
    (maxSumFreeSize n : ℝ) ≥ (n + 2) / 3 := by
  sorry

/--
Erdős Problem 792, best known lower bound (Bedert [Be25b]):
There exists $c > 0$ such that $f(n) \geq n/3 + c \cdot \log(\log(n))$ for all
sufficiently large $n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_792.variants.lower_bedert :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxSumFreeSize n : ℝ) ≥ n / 3 + c * Real.log (Real.log n) := by
  sorry

/--
Erdős Problem 792, best known upper bound (Eberhard–Green–Manners [EGM14]):
$f(n) \leq n/3 + o(n)$, i.e., for every $\varepsilon > 0$,
$f(n) \leq (1/3 + \varepsilon) \cdot n$ for all sufficiently large $n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_792.variants.upper_egm :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxSumFreeSize n : ℝ) ≤ (1 / 3 + ε) * n := by
  sorry

end Erdos792
