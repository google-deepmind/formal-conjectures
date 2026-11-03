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
# Erdős Problem 1100

*References:*
- [erdosproblems.com/1100](https://www.erdosproblems.com/1100)
- [ErHa78] Erdős, P. and Hall, R. R., *On some unconventional problems on the divisors of
  integers*. J. Austral. Math. Soc. Ser. A 25 (1978), 479-485.
  [PDF](https://www.renyi.hu/~p_erdos/1978-26.pdf)
- [Er81h] Erdős, P., *Some problems and results on additive and multiplicative number theory*.
  Analytic number theory (Philadelphia, Pa., 1980) (1981), 171-182.
  [PDF](https://www.renyi.hu/~p_erdos/1981-33.pdf)
- [ErTe89] Erdős, P. and Tenenbaum, G., *Sur les fonctions arithmétiques liées aux diviseurs
  consécutifs*. J. Number Theory 31 (1989), 285-311.
  [PDF](https://www.renyi.hu/~p_erdos/1989-37.pdf)

The function $\tau_\perp(n)$ is called $\tau_r(n)$ in [Er81h] and $f(n)$ in [ErHa78] and [ErTe89].
-/

@[expose] public section

open Filter Asymptotics
open scoped ArithmeticFunction.omega

namespace Erdos1100

/-- $\tau_\perp(n)$ is the number of indices $i$ such that the divisors $d_i<d_{i+1}$ of $n$ that
are consecutive in increasing order are coprime. As in `Erdos1099`, `Nat.nth (· ∣ n) i` is the
$(i+1)$-th smallest divisor of `n` (counting from $0$), and `i` runs over the $\tau(n)-1$ pairs of
consecutive divisors. For $n = 0$ and $n = 1$ there are no such pairs and the value is $0$. -/
noncomputable def tauPerp (n : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin (n.divisors.card - 1) ↦
    Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) ((i : ℕ) + 1))).card

/-- $g(k)$ is the maximum of $\tau_\perp(n)$ over the squarefree $n$ with $\omega(n)=k$. The set of
values is nonempty (take $n$ a product of $k$ distinct primes) and bounded by $2^k$, because
$\tau_\perp(n)<\tau(n)=2^k$, so `sSup` is a true maximum. -/
noncomputable def g (k : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ n : ℕ, Squarefree n ∧ ω n = k ∧ tauPerp n = t}

/--
If $1=d_1<\cdots<d_{\tau(n)}=n$ are the divisors of $n$, then let $\tau_\perp(n)$ count the number
of $i$ for which $(d_i,d_{i+1})=1$.

Is it true that $\tau_\perp(n)/\omega(n)\to \infty$ for almost all $n$?

This is the first part, asked by Erdős and Hall [ErHa78, p. 483]. We read it as: for every $C$ the
set of $n$ with $\tau_\perp(n)\leq C\omega(n)$ has natural density $0$. This is equivalent to
$\tau_\perp(n)/\omega(n)\to\infty$ along a set of density $1$, and it avoids dividing by
$\omega(1)=0$.

The answer is yes. By [ErTe89, Corollary 2, p. 288], $\tau_\perp(n)\geq(\log n)^{\log 3-1+o(1)}$
for almost all $n$ (see `erdos_1100.variants.normal_order`), while $\omega(n)\sim\log\log n$ for
almost all $n$ (Hardy-Ramanujan).
-/
@[category research solved, question, AMS 11]
theorem erdos_1100.parts.i :
    ∀ C : ℝ, {n : ℕ | (tauPerp n : ℝ) ≤ C * (ω n : ℝ)}.HasDensity 0 := by
  sorry

/--
If $1=d_1<\cdots<d_{\tau(n)}=n$ are the divisors of $n$, then let $\tau_\perp(n)$ count the number
of $i$ for which $(d_i,d_{i+1})=1$.

Is it true that
$$\tau_\perp(n)< \exp((\log n)^{o(1)})$$
for all $n$?

This is the second part. Erdős and Hall [ErHa78, p. 483] say it would be reasonable to expect
that for every $\epsilon>0$ one has $\tau_\perp(n)<\exp((\log n)^{\epsilon})$; the problem page
asks it as a question. We read $o(1)$ as: for every $\epsilon>0$ and all sufficiently large $n$.
This is equivalent to a bound for all $n$ with an exponent that tends to $0$. A bound for all $n$
with a fixed small $\epsilon$ fails: for example $\tau_\perp(30)=4>\exp((\log 30)^{0.1})$.

The answer is no. Erdős and Tenenbaum [ErTe89, Theorem 4, p. 289] proved
$\max_{n\leq x}\tau_\perp(n)\geq\exp\bigl(((\log 2)^2+o(1))\log x/(\log\log x)^2\bigr)$ (see
`erdos_1100.variants.erdos_tenenbaum_max`). This gives infinitely many $n$ with
$\tau_\perp(n)>\exp((\log n)^{1/2})$.
-/
@[category research solved, question, AMS 11]
theorem erdos_1100.parts.ii :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (tauPerp n : ℝ) < Real.exp (Real.log n ^ ε) := by
  sorry

def erdos_1100.parts.iii.answer : ℕ → ℝ := sorry

/--
Let
$$g(k) = \max_{\omega(n)=k}\tau_\perp(n),$$
where $\omega(n)$ counts the number of distinct prime divisors of $n$, and $n$ is restricted to
squarefree integers. Determine the growth of $g(k)$.

This is the third part. We read "determine the growth" as $g(k)=\Theta(\texttt{answer}\ k)$. Known
bounds are $(\sqrt2+o(1))^k<g(k)<(2-c)^k$ [Er81h, p. 173] (see
`erdos_1100.variants.erdos_simonovits`), and $g(k)\leq 3\cdot(3\cdot 2^{-2/3})^k$
[ErTe89, Theorem 1] (see `erdos_1100.variants.erdos_tenenbaum_g`). So $g$ is at most exponential,
the lower bound announced in [Er81h] would make it exponential, and already the base of the
exponential is open.
-/
@[category research open, question value, AMS 11]
theorem erdos_1100.parts.iii :
    (fun k : ℕ ↦ (g k : ℝ)) =Θ[atTop] erdos_1100.parts.iii.answer := by
  sorry

/--
It is trivial that $\tau_\perp(n)\geq \omega(n)$ [ErHa78, p. 480], [ErTe89, (1.9), p. 288]: each
prime divisor of $n$ is the larger member of a coprime pair of consecutive divisors.
-/
@[category textbook, AMS 11]
theorem erdos_1100.variants.omega_le : ∀ n : ℕ, 0 < n → ω n ≤ tauPerp n := by
  sorry

/--
There is equality $\tau_\perp(n)=\omega(n)$ for infinitely many $n$: Erdős and Hall [ErHa78, p. 480]
note equality when $n=p_1\cdots p_k$ and $p_i>p_1\cdots p_{i-1}$ for $2\leq i\leq k$. Such $n$
exist for every $k$, which we state.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.eq_omega (k : ℕ) :
    ∃ n : ℕ, Squarefree n ∧ ω n = k ∧ tauPerp n = k := by
  sorry

/--
Erdős and Hall [ErHa78, Theorem 1, p. 480] prove, for all $\epsilon>0$ and sufficiently large $x$,
$$\max_{n<x} \tau_\perp(n) > \exp((\log\log x)^{2-\epsilon}).$$
We write the maximum as: some $n<x$ has $\tau_\perp(n)$ above the bound.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.erdos_hall : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    ∃ n : ℕ, (n : ℝ) < x ∧ Real.exp (Real.log (Real.log x) ^ (2 - ε)) < (tauPerp n : ℝ) := by
  sorry

/--
Erdős and Tenenbaum [ErTe89, Theorem 4, p. 289] improved this considerably: for $x\geq 3$,
$$\max_{n\leq x}\tau_\perp(n)\geq \exp\Bigl(\bigl((\log 2)^2+o(1)\bigr)
\frac{\log x}{(\log\log x)^2}\Bigr).$$
We write $o(1)$ as an arbitrarily small $\delta>0$ and the maximum as: some $n\leq x$ has
$\tau_\perp(n)$ above the bound.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.erdos_tenenbaum_max : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
    ∃ n : ℕ, (n : ℝ) ≤ x ∧
      Real.exp (((Real.log 2) ^ 2 - δ) * Real.log x / (Real.log (Real.log x)) ^ 2) ≤
        (tauPerp n : ℝ) := by
  sorry

/--
Erdős and Tenenbaum [ErTe89, Corollary 2, p. 288] proved that for almost all $n$ (that is, on a set
of density $1$)
$$(\log n)^{\log 3-1+o(1)}\leq \tau_\perp(n)\leq (\log n)^{\log 2-1/2+o(1)}.$$
The paper credits the upper bound to an earlier work of the same authors (Bull. Soc. Math. France
111 (1983)). We write $o(1)$ as: for every $\epsilon>0$ the set of $n$ with
both bounds, with exponents shifted by $\mp\epsilon$, has density $1$.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.normal_order : ∀ ε : ℝ, 0 < ε →
    {n : ℕ | Real.log n ^ (Real.log 3 - 1 - ε) ≤ (tauPerp n : ℝ) ∧
      (tauPerp n : ℝ) ≤ Real.log n ^ (Real.log 2 - 1 / 2 + ε)}.HasDensity 1 := by
  sorry

/--
Erdős and Simonovits (see [Er81h, p. 173]) proved
$$(2^{1/2}+o(1))^k < g(k) < (2-c)^k$$
for some constant $c>0$. We write the lower bound as: every fixed $0\leq r<\sqrt2$ satisfies
$r^k<g(k)$ for all large $k$, and the upper bound for all large $k$.

[Er81h] announces this without proof, and [ErTe89, p. 291] calls the argument of Erdős and
Simonovits for squarefree $n$, which it uses for the upper bound, unpublished. The upper bound also
follows from `erdos_1100.variants.erdos_tenenbaum_g`.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.erdos_simonovits :
    (∀ r : ℝ, 0 ≤ r → r < Real.sqrt 2 → ∀ᶠ k : ℕ in atTop, r ^ k < (g k : ℝ)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop, (g k : ℝ) < (2 - c) ^ k := by
  sorry

/--
For squarefree $n$ with $\omega(n)=k$ the bound $f(n)\leq 3\tau(n)B_1^{\omega_1(n)}$ of
[ErTe89, Theorem 1, (1.3), p. 287], with $B_1=3\cdot 2^{-5/3}$, gives
$$g(k)\leq 3\left(3\cdot 2^{-2/3}\right)^k,$$
and $3\cdot 2^{-2/3}=1.88988\ldots<2$.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.erdos_tenenbaum_g (k : ℕ) :
    (g k : ℝ) ≤ 3 * (3 / (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ k := by
  sorry

end Erdos1100
