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
# Erdős Problem 929

*References:*
- [erdosproblems.com/929](https://www.erdosproblems.com/929)
- [Er76d] Erdős, P., *Problems and results on number theoretic properties of consecutive integers
  and related questions*. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics
  (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.
  [PDF](https://www.renyi.hu/~p_erdos/1976-39.pdf)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos929

/-- Each of the integers `n + 1, …, n + k` is divisible by some prime `≤ x`. -/
def AllHaveSmallPrimeFactor (x k n : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 k, ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ p ∣ n + i

/-- $S(k)$ is the least $x$ such that the set of $n$ for which each of $n+1, \ldots, n+k$ is
divisible by a prime $\leq x$ has positive density.

The set of such $n$ is periodic modulo the product of the primes $\leq x$, so its density exists.
We let $x$ range over `ℕ`: only the primes $\leq x$ matter, so the least $x$ is a prime and nothing
changes if $x$ is real. For every `k` the value `x = k + 1` is admissible (take
$n \equiv 1 \pmod{(k+1)!}$), so `sInf` is a true minimum. For `k = 0` the condition is vacuous and
`S 0 = 0`. -/
noncomputable def S (k : ℕ) : ℕ :=
  sInf {x : ℕ | {n : ℕ | AllHaveSmallPrimeFactor x k n}.HasPosDensity}

/-- If the set of `n` such that each of `n + 1, …, n + k` is divisible by a prime `≤ x` has
positive density, then `S k ≤ x`. -/
@[category API, AMS 11]
theorem S_le {k x : ℕ} (h : {n : ℕ | AllHaveSmallPrimeFactor x k n}.HasPosDensity) :
    S k ≤ x := by
  unfold S
  exact Nat.sInf_le h

def erdos_929.parts.i.answer : ℕ → ℝ := sorry

/--
Let $k\geq 2$ be large and let $S(k)$ be the minimal $x$ such that there is a positive density set
of $n$ where
$$n+1,n+2,\ldots,n+k$$
are all divisible by primes $\leq x$.

Estimate $S(k)$ - in particular, is it true that $S(k)\geq k^{1-o(1)}$?

A problem of Erdős [Er76d, p. 26]. This is the first part. We read "estimate" as
$S(k) = \Theta(\text{answer})$ as $k \to \infty$.
-/
@[category research open, question value, AMS 11]
theorem erdos_929.parts.i : (fun k ↦ (S k : ℝ)) =Θ[atTop] erdos_929.parts.i.answer := by
  sorry

/--
Let $k\geq 2$ be large and let $S(k)$ be the minimal $x$ such that there is a positive density set
of $n$ where
$$n+1,n+2,\ldots,n+k$$
are all divisible by primes $\leq x$.

Estimate $S(k)$ - in particular, is it true that $S(k)\geq k^{1-o(1)}$?

This is the second part. We read $o(1)$ as an arbitrary $\varepsilon > 0$ for all large $k$.
-/
@[category research open, question, AMS 11]
theorem erdos_929.parts.ii :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ (1 - ε) ≤ (S k : ℝ) := by
  sorry

/--
It follows from Rosser's sieve that $S(k)> k^{1/2-o(1)}$.

Erdős [Er76d, p. 26] states this for the index $\ell$ with $p_\ell = S(k)$. Since
$S(k) = p_\ell \geq \ell$, the bound transfers to $S(k)$. The $o(1)$ is stated with an arbitrary
$\varepsilon > 0$.
-/
@[category research solved, AMS 11]
theorem erdos_929.variants.rosser :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (S k : ℝ) := by
  sorry

/--
It is trivial that $S(k)\leq k+1$ since, for example, one can take $n\equiv 1\pmod{(k+1)!}$.
-/
@[category textbook, AMS 11]
theorem erdos_929.variants.trivial_upper (k : ℕ) : S k ≤ k + 1 := by
  sorry

end Erdos929
