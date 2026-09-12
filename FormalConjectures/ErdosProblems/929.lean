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

import FormalConjecturesUtil

/-!
# Erdős Problem 929

*References:*
- [erdosproblems.com/929](https://www.erdosproblems.com/929)
- [Er76d] Erdős, P., *Problems and results on number theoretic properties of consecutive integers
  and related questions*. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics
  (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.
- [FGKMT18] Ford, Kevin and Green, Ben and Konyagin, Sergei and Maynard, James and Tao, Terence,
  *Long gaps between primes*. J. Amer. Math. Soc. (2018), 65-105.
-/

open Filter Real

namespace Erdos929

/--
`ConsecutiveHaveSmallPrimeFactor x n k` means that each of $n+1,\ldots,n+k$ is divisible by some
prime $\leq x$ (equivalently, has a prime factor at most $x$).
-/
def ConsecutiveHaveSmallPrimeFactor (x n k : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 k, ∃ p ≤ x, Nat.Prime p ∧ p ∣ n + i

/--
`S k` is the least $x$ such that there is a positive density set of $n$ for which
`ConsecutiveHaveSmallPrimeFactor x n k` holds.
-/
noncomputable def S (k : ℕ) : ℕ :=
  sInf {x | ∃ A : Set ℕ, A.HasPosDensity ∧ ∀ n ∈ A, ConsecutiveHaveSmallPrimeFactor x n k}

/--
Let $k\geq 2$ be large and let $S(k)$ be the minimal $x$ such that there is a positive density set
of $n$ where
$$n+1,n+2,\ldots,n+k$$
are all divisible by primes $\leq x$.

Estimate $S(k)$ - in particular, is it true that $S(k)\geq k^{1-o(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_929 : answer(sorry) ↔
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ (1 - o k) ≤ S k := by
  sorry

/--
It follows from Rosser's sieve that $S(k)> k^{1/2-o(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_929.variants.rosser :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ ((1 : ℝ) / 2 - o k) < S k := by
  sorry

/--
It is trivial that $S(k)\leq k+1$ since, for example, one can take $n\equiv 1\pmod{(k+1)!}$.
-/
@[category research solved, AMS 11]
theorem erdos_929.variants.trivial : ∀ k ≥ 2, S k ≤ k + 1 := by
  sorry

/--
The best bound on large gaps between primes due to Ford, Green, Konyagin, Maynard, and Tao
[FGKMT18] (see [erdosproblems.com/4](https://www.erdosproblems.com/4)) implies
$$S(k) \ll k \frac{\log\log\log k}{\log\log k\log\log\log\log k}.$$
-/
@[category research solved, AMS 11]
theorem erdos_929.variants.fgkmt :
    (fun k ↦ (S k : ℝ)) ≪ fun k ↦
      (k : ℝ) * log (log (log k)) / (log (log k) * log (log (log (log k)))) := by
  sorry

end Erdos929
