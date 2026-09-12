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
# Erdős Problem 978

*References:*
- [erdosproblems.com/978](https://www.erdosproblems.com/978)
- [Br11] Browning, T. D., *The polynomial sieve and equal sums of like powers*.
  Int. Math. Res. Not. IMRN (2011), 331-349.
- [Er53] Erdős, P., *Arithmetical properties of polynomials*. J. London Math. Soc. (1953), 416-425.
- [He06] Heath-Brown, D. R., *Power-free values of polynomials*. Quart. J. Math. (2006), 67-88.
- [Ho67] Hooley, C., *On the power-free values of polynomials*. Mathematika (1967), 21-26.
-/

open Filter Polynomial Set
open scoped Topology

namespace Erdos978

/-- `n` is `k`-power-free if it is not divisible by `p^k` for any prime `p`. -/
def IsPowFree (k n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ^ k ∣ n

/-- Polynomials considered in the boxed problem: irreducible of degree `k>2` not a power of `2`,
with positive leading coefficient. -/
def IsAdmissible (f : ℤ[X]) : Prop :=
  Irreducible f ∧ 2 < f.natDegree ∧ (∀ l : ℕ, f.natDegree ≠ 2 ^ l) ∧ 0 < f.leadingCoeff

/--
Let $f\in \mathbb{Z}[x]$ be an irreducible polynomial of degree $k>2$ (and suppose that
$k\neq 2^l$ for any $l\geq 1$) such that the leading coefficient of $f$ is positive.
Does the set of integers $n\geq 1$ for which $f(n)$ is $(k-1)$-power-free have positive density?
-/
@[category research solved, AMS 11]
theorem erdos_978.parts.i :
    ∀ f : ℤ[X], IsAdmissible f →
      { n : ℕ | 0 < n ∧
          IsPowFree (f.natDegree - 1) (f.aeval (n : ℤ)).natAbs }.HasPosDensity := by
  sorry

/--
If $k>3$, and for all primes $p$ there exists $n$ such that $p^{k-2}\nmid f(n)$, then are there
infinitely many $n$ for which $f(n)$ is $(k-2)$-power-free?
-/
@[category research open, AMS 11]
theorem erdos_978.parts.ii :
    answer(sorry) ↔
      ∀ f : ℤ[X], IsAdmissible f → 3 < f.natDegree →
        (∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.aeval n) →
          { n : ℕ | 0 < n ∧
            IsPowFree (f.natDegree - 2) (f.aeval (n : ℤ)).natAbs }.Infinite := by
  sorry

/--
In particular, does
$$
n^4+2
$$
represent infinitely many squarefree numbers?
-/
@[category research open, AMS 11]
theorem erdos_978.parts.iii :
    answer(sorry) ↔
      { n : ℕ | Squarefree ((n : ℤ) ^ 4 + 2).natAbs }.Infinite := by
  sorry

/--
Hooley [Ho67] settled the first question, in fact providing a precise asymptotic for the number
of such $n\leq x$.
-/
@[category research solved, AMS 11]
theorem erdos_978.variants.hooley (f : ℤ[X]) (hf : IsAdmissible f) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun x : ℕ ↦
        (({n : ℕ | n < x ∧ 0 < n ∧
            IsPowFree (f.natDegree - 1) (f.aeval (n : ℤ)).natAbs }).ncard : ℝ) / x)
        atTop (𝓝 c) := by
  sorry

end Erdos978
