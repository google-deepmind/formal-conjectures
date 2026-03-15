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
# Erdős Problem 448

*Reference:* [erdosproblems.com/448](https://www.erdosproblems.com/448)

Let $\tau(n)$ count the divisors of $n$ and $\tau^+(n)$ count the number of $k$
such that $n$ has a divisor in $[2^k, 2^{k+1})$. Is it true that, for all
$\epsilon > 0$, $\tau^+(n) < \epsilon \tau(n)$ for almost all $n$?

This was disproved by Erdős and Tenenbaum [ErTe81], who showed that for every
$\epsilon > 0$, the upper density of $\{n : \tau^+(n) \geq \epsilon \tau(n)\}$
is $\asymp \epsilon^{1-o(1)}$ (positive for each fixed $\epsilon$).

Hall and Tenenbaum [HaTe88] showed the upper density is
$\ll \epsilon \log(2/\epsilon)$ and proved that $\tau^+(n)/\tau(n)$ has a
distribution function.

Ford [Fo08] answered a follow-up question, proving an asymptotic formula
$\sum_{n \leq x} \tau^+(n) \asymp x (\log x)^{1-\alpha} / (\log \log x)^{3/2}$
where $\alpha = 1 - (1 + \log \log 2)/\log 2 \approx 0.08607$.

See also problems #446 and #449.

[Er79] Erdős, P., _Some unconventional problems in number theory_ (1979).

[Er79e] Erdős, P., _Some unconventional problems in number theory_ (1979).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980), p. 89.

[Er81h] Erdős, P., _Some problems and results in number theory_ (1981), p. 173.

[ErTe81] Erdős, P. and Tenenbaum, G., _Sur la structure de la suite des diviseurs d'un entier_.
Ann. Inst. Fourier (Grenoble) **31** (1981), 17–37.

[HaTe88] Hall, R. R. and Tenenbaum, G., _Divisors_. Cambridge Tracts in Mathematics (1988).

[Fo08] Ford, K., _The distribution of integers with a divisor in a given interval_. Ann. of Math.
(2) **168** (2008), 367–433.
-/

open Finset Classical

namespace Erdos448

/-- $\tau^+(n)$: the number of $k \in \mathbb{N}$ such that $n$ has a divisor $d$ with
$2^k \leq d < 2^{k+1}$.

`Finset.range n` suffices because any divisor $d$ of $n$ satisfies $d \leq n$,
so $2^k \leq d \leq n$ implies $k \leq \log_2(n) < n$ for $n \geq 1$. -/
noncomputable def tauPlus (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k =>
    (n.divisors.filter (fun d => 2 ^ k ≤ d ∧ d < 2 ^ (k + 1))).Nonempty)).card

/-- Erdős Problem 448 (disproved by Erdős–Tenenbaum [ErTe81]):
Is it true that, for all $\epsilon > 0$, $\tau^+(n) < \epsilon \tau(n)$ for almost all $n$?
The answer is no. -/
@[category research solved, AMS 11]
theorem erdos_448 : answer(False) ↔
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((Finset.Icc 1 N).filter (fun n =>
        (tauPlus n : ℝ) ≥ ε * (n.divisors.card : ℝ))).card / (N : ℝ) < δ := by
  sorry

/-- Stronger result by Erdős–Tenenbaum [ErTe81]: for every $\epsilon > 0$, the upper density
of $\{n : \tau^+(n) \geq \epsilon \cdot \tau(n)\}$ is positive. -/
@[category research solved, AMS 11]
theorem erdos_448.variants.upper_density :
    ∀ ε : ℝ, ε > 0 →
    ∃ c : ℝ, c > 0 ∧
      ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
        c ≤ ((Finset.Icc 1 N).filter (fun n =>
          (tauPlus n : ℝ) ≥ ε * (n.divisors.card : ℝ))).card / (N : ℝ) := by
  sorry

end Erdos448
