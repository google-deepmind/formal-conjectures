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
import FormalConjecturesForMathlib.Data.Nat.MaxPrimeFac
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 928

*Reference:* [erdosproblems.com/928](https://www.erdosproblems.com/928)

*Related:* [Erdős Problem 370](https://www.erdosproblems.com/370)

Let $\alpha, \beta \in (0,1)$ and let $P(n)$ denote the largest prime divisor of $n$.
Does the density of integers $n$ such that $P(n) < n^\alpha$ and $P(n+1) < (n+1)^\beta$
exist?

Erdős asked whether the events $P(n) < n^\alpha$ and $P(n+1) < (n+1)^\beta$ are independent,
in the sense that the density of $n$ satisfying both conditions equals
$\rho(1/\alpha) \cdot \rho(1/\beta)$, where $\rho$ is the Dickman function.

Dickman [Di30] showed the density of smooth $n$, with largest prime factor $< n^\alpha$,
is $\rho(1/\alpha)$.

Schinzel [Sc67b] showed that for infinitely many $n$, the largest prime factor of $n(n+1)$
is at most $n^{O(1/\log \log n)}$.

Teräväinen [Te18] proved the logarithmic density exists and equals
$\rho(1/\alpha) \rho(1/\beta)$.
Wang [Wa21] proved the natural density equals $\rho(1/\alpha) \rho(1/\beta)$ assuming the
Elliott–Halberstam conjecture for friable integers.

[Er76d] Erdős, P., *Problems in number theory and combinatorics*.

[ErPo78] Erdős, P. and Pomerance, C., *On the largest prime factors of n and n+1*.
Aequationes Math. **17** (1978), 311–321.

[Di30] Dickman, K., *On the frequency of numbers containing prime factors of a certain
relative magnitude*. Ark. Mat. Astr. Fys. **22A** (1930), 1–14.

[Sc67b] Schinzel, A., *On two theorems of Gelfond and some of their applications*.
Acta Arith. **13** (1967/68), 177–236.

[Te18] Teräväinen, J., *On binary correlations of multiplicative functions*. Forum Math.
Sigma **6** (2018), e10.

[Wa21] Wang, Z., *Three conjectures on P⁺(n) and P⁺(n+1) hold under the
Elliott–Halberstam conjecture for friable integers*. J. Number Theory **228** (2021), 1–11.
-/

open Set Filter

namespace Erdos928

/-- The Dickman function $\rho : \mathbb{R} \to \mathbb{R}$, the unique continuous function
satisfying $\rho(u) = 1$ for $0 \le u \le 1$ and $u \rho'(u) = -\rho(u-1)$ for $u > 1$. -/
opaque dickmanRho : ℝ → ℝ

/-- The set of $n \ge 2$ with $P(n) < n^\alpha$ and $P(n+1) < (n+1)^\beta$. -/
def smoothConsecutiveSet (α β : ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 2 ∧
    (Nat.maxPrimeFac n : ℝ) < (n : ℝ) ^ α ∧
    (Nat.maxPrimeFac (n + 1) : ℝ) < ((n + 1 : ℕ) : ℝ) ^ β}

/--
Erdős Problem 928 [Er76d][ErPo78]:

For $\alpha, \beta \in (0,1)$, the natural density of integers $n$ with $P(n) < n^\alpha$ and
$P(n+1) < (n+1)^\beta$ exists and equals $\rho(1/\alpha) \cdot \rho(1/\beta)$, where $\rho$ is
the Dickman function. This asserts independence of the smooth-number events for consecutive
integers.
-/
@[category research open, AMS 11]
theorem erdos_928 : answer(sorry) ↔
    ∀ α β : ℝ, 0 < α → α < 1 → 0 < β → β < 1 →
    (smoothConsecutiveSet α β).HasDensity
      (dickmanRho (1 / α) * dickmanRho (1 / β)) := by
  sorry

end Erdos928
