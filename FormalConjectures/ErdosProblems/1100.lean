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
# Erdős Problem 1100

*References:*
- [erdosproblems.com/1100](https://www.erdosproblems.com/1100)
- [ErHa78] Erdős, P. and Hall, R. R., *On some unconventional problems on the divisors of
  integers*. J. Austral. Math. Soc. Ser. A (1978), 479--485.
- [Er81h] Erdős, P., *Some problems and results on additive and multiplicative number theory*.
  Analytic number theory (Philadelphia, Pa., 1980) (1981), 171-182.
-/

open Filter Asymptotics Real
open scoped Topology ArithmeticFunction.omega

namespace Erdos1100

/--
`τ_⊥(n)` counts the number of consecutive coprime pairs among the divisors of `n`,
written in increasing order.
-/
def tauPerp (n : ℕ) : ℕ :=
  let ds := n.divisors.sort (· ≤ ·)
  (ds.zip ds.tail).countP fun p => Nat.Coprime p.1 p.2

/--
$g(k)$ is the maximum of $\tau_\perp(n)$ over squarefree $n$ with $\omega(n)=k$.
-/
noncomputable def g (k : ℕ) : ℕ :=
  sSup {tauPerp n | (n : ℕ) (_ : Squarefree n) (_ : ω n = k)}

/-- The maximum of $\tau_\perp(n)$ over $n < x$. -/
def maxTauPerpLT (x : ℕ) : ℕ :=
  (Finset.range x).sup tauPerp

/-- Sanity check: $n=1$ has a single divisor, so $\tau_\perp(1)=0$. -/
@[category test, AMS 11]
theorem tauPerp_one : tauPerp 1 = 0 := by native_decide

/-- Sanity check: a prime has divisors $1,p$ with $(1,p)=1$, so $\tau_\perp(p)=1$. -/
@[category test, AMS 11]
theorem tauPerp_two : tauPerp 2 = 1 := by native_decide

/-- Sanity check: the divisors of $6$ are $1,2,3,6$, and exactly two consecutive pairs
are coprime. -/
@[category test, AMS 11]
theorem tauPerp_six : tauPerp 6 = 2 := by native_decide

/-- Sanity check: the divisors of $30$ are $1,2,3,5,6,10,15,30$, and exactly four
consecutive pairs are coprime. -/
@[category test, AMS 11]
theorem tauPerp_thirty : tauPerp 30 = 4 := by native_decide

/--
If $1=d_1<\cdots<d_{\tau(n)}=n$ are the divisors of $n$, then let $\tau_\perp(n)$ count the number of $i$ for which $(d_i,d_{i+1})=1$.

Is it true that $\tau_\perp(n)/\omega(n)\to \infty$ for almost all $n$?
-/
@[category research open, AMS 11]
theorem erdos_1100.parts.i : answer(sorry) ↔
    ∃ A : Set ℕ, A.HasDensity 1 ∧
      Tendsto (fun n ↦ (tauPerp n : ℝ) / (ω n : ℝ)) (atTop ⊓ 𝓟 A) atTop := by
  sorry

/--
If $1=d_1<\cdots<d_{\tau(n)}=n$ are the divisors of $n$, then let $\tau_\perp(n)$ count the number of $i$ for which $(d_i,d_{i+1})=1$.

Is it true that
$$\tau_\perp(n)< \exp((\log n)^{o(1)})$$
for all $n$?
-/
@[category research open, AMS 11]
theorem erdos_1100.parts.ii : answer(sorry) ↔
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ n ≥ 2,
      (tauPerp n : ℝ) < exp (log n ^ o n) := by
  sorry

/--
Let
$$g(k) = \max_{\omega(n)=k}\tau_\perp(n),$$
where $\omega(n)$ counts the number of distinct prime divisors of $n$, and $n$ is restricted to squarefree integers. Determine the growth of $g(k)$.
-/
@[category research open, AMS 11]
theorem erdos_1100.parts.iii :
    (fun k ↦ (g k : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
It is trivial that $\tau_\perp(n)\geq \omega(n)$ (with equality for infinitely many $n$).
-/
@[category textbook, AMS 11]
theorem erdos_1100.variants.lower_bound (n : ℕ) : ω n ≤ tauPerp n := by
  sorry

/--
It is trivial that $\tau_\perp(n)\geq \omega(n)$ (with equality for infinitely many $n$).
-/
@[category textbook, AMS 11]
theorem erdos_1100.variants.equality_infinitely_often :
    {n | tauPerp n = ω n}.Infinite := by
  sorry

/--
Erdős and Hall prove, for all $\epsilon>0$ and sufficiently large $x$,
$$\max_{n<x} \tau_\perp(n) > \exp((\log\log x)^{2-\epsilon}).$$
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.erdos_hall (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      exp (log (log x) ^ (2 - ε)) < (maxTauPerpLT x : ℝ) := by
  sorry

/--
Erdős and Simonovits (see [Er81h]) proved
$$(2^{1/2}+o(1))^k < g(k) < (2-c)^k$$
for some constant $c>0$.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.erdos_simonovits :
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)) (c : ℝ) (_ : 0 < c),
      ∀ᶠ k in atTop,
        (√2 + o k) ^ k < (g k : ℝ) ∧ (g k : ℝ) < (2 - c) ^ k := by
  sorry

end Erdos1100
