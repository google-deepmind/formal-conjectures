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
# Erdős Problem 928

*References:*
- [erdosproblems.com/928](https://www.erdosproblems.com/928)
- [Di30] Dickman, K., *On the frequency of numbers containing prime factors of a certain relative
  magnitude*. Ark. Mat. Astr. Fys. (1930), 1-14.
- [Er76d] Erdős, P., *Problems and results on number theoretic properties of consecutive integers
  and related questions*. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics
  (1976), 25-44.
- [Er76e] Erdős, P., *Problems and results on consecutive integers*. Publ. Math. Debrecen (1976),
  271-282.
- [ErPo78] Erdős, Paul and Pomerance, Carl, *On the largest prime factors of $n$ and $n+1$*.
  Aequationes Math. (1978), 311-321.
- [Te18] Teräväinen, Joni, *On binary correlations of multiplicative functions*. Forum Math. Sigma
  (2018), Paper No. e10, 41.
- [Wa21] Wang, Zhiwei, *Three conjectures on $P^+(n)$ and $P^+(n+1)$ hold under the
  Elliott-Halberstam conjecture for friable integers*. J. Number Theory (2021), 1--11.
-/

@[expose] public section

namespace Erdos928

/-- The set of $n$ with $P(n)<n^{\alpha}$ and $P(n+1)<(n+1)^{\beta}$, where $P(m)$ is the
largest prime divisor of $m$ (`Nat.maxPrimeFac`). The junk values at $n = 0, 1$ do not affect
densities. -/
def S (α β : ℝ) : Set ℕ :=
  {n | (n.maxPrimeFac : ℝ) < (n : ℝ) ^ α ∧ ((n + 1).maxPrimeFac : ℝ) < ((n + 1 : ℕ) : ℝ) ^ β}

/--
Let $\alpha,\beta\in (0,1)$ and let $P(n)$ denote the largest prime divisor of $n$. Does the
density of integers $n$ such that $P(n)<n^{\alpha}$ and $P(n+1)<(n+1)^\beta$ exist?

Teräväinen [Te18] proved that the logarithmic density exists and equals
$\rho(1/\alpha)\rho(1/\beta)$, where $\rho$ is the Dickman function.
-/
@[category research open, question, AMS 11]
theorem erdos_928 :
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∃ d : ℝ, (S α β).HasDensity d := by
  sorry

end Erdos928
