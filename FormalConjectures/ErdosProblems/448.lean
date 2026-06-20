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

*References:*
- [erdosproblems.com/448](https://www.erdosproblems.com/448)
- [Er79] Erdős, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.
- [Er79e] Erdős, Paul, Some unconventional problems in number theory. Astérisque (1979), 73-82.
- [HaTe88] Hall, Richard R. and Tenenbaum, Gérald, Divisors. (1988), xvi+167.
- [ErTe81] Erdős, P., Tenenbaum, G., *Sur la structure de la suite des diviseurs d'un entier.*
  Ann. Inst. Fourier (Grenoble) **31** (1981), 17–37.
- [Fo08] Ford, Kevin, *The distribution of integers with a divisor in a given interval.*
  Ann. of Math. (2) **168** (2008), 367–433.
-/

namespace Erdos448

open Filter Asymptotics Topology

/-- `tauPlus n` (written $\tau^+(n)$) counts the number of $k$ such that $n$ has a divisor in
$[2^k, 2^{k+1})$. Equivalently, the number of distinct values $\lfloor \log_2 d \rfloor$ as $d$
ranges over the divisors of $n$: a divisor $d$ lies in $[2^k, 2^{k+1})$ iff `Nat.log 2 d = k`. -/
def tauPlus (n : ℕ) : ℕ := (n.divisors.image (Nat.log 2)).card

/-- Sanity check: $\tau^+(6) = 3$. Divisors $1, 2, 3, 6$ lie in dyadic blocks $k = 0, 1, 1, 2$,
so the distinct blocks are $\{0, 1, 2\}$. ($\tau(6) = 4$.) -/
@[category test, AMS 11]
theorem tauPlus_six : tauPlus 6 = 3 := by decide

/-- Sanity check: $\tau^+(12) = 4$. Divisors $1, 2, 3, 4, 6, 12$ lie in dyadic blocks
$k = 0, 1, 1, 2, 2, 3$, so the distinct blocks are $\{0, 1, 2, 3\}$. ($\tau(12) = 6$.) -/
@[category test, AMS 11]
theorem tauPlus_twelve : tauPlus 12 = 4 := by decide

/-- Always $\tau^+(n) \le \tau(n)$: the occupied dyadic blocks are the image of the divisor set
under `Nat.log 2`, and an image has at most as many elements as its source. This is what makes the
$\epsilon < 1$ comparison in the problem meaningful. -/
@[category test, AMS 11]
theorem tauPlus_le_tau (n : ℕ) : tauPlus n ≤ n.divisors.card :=
  Finset.card_image_le

/--
Let $\tau(n)$ count the divisors of $n$ and $\tau^+(n)$ count the number of $k$ such that $n$ has a
divisor in $[2^k, 2^{k+1})$. Is it true that, for all $\epsilon > 0$,
$$ \tau^+(n) < \epsilon \cdot \tau(n) $$
for almost all $n$?

This is false, and was disproved by Erdős and Tenenbaum [ErTe81], who showed that in fact the upper
density of the set of such $n$ is $\asymp \epsilon^{1-o(1)}$ (where the $o(1)$ in the exponent
$\to 0$ as $\epsilon \to 0$). A more precise result was proved by Hall and Tenenbaum [HaTe88]
(see Section 4.6), who showed that the upper density is $\ll \epsilon \log(2/\epsilon)$. Hall and
Tenenbaum further prove that $\tau^+(n)/\tau(n)$ has a distribution function. Erdős and Graham also
asked whether there is a good inequality known for $\sum_{n \leq x} \tau^+(n)$. This was provided by
Ford [Fo08] who proved
$$ \sum_{n \leq x} \tau^+(n) \asymp x\frac{(\log x)^{1-\alpha}}{(\log\log x)^{3/2}} $$
where
$$ \alpha = 1-\frac{1+\log\log 2}{\log 2} = 0.08607\cdots. $$
-/
@[category research solved, AMS 11]
theorem erdos_448 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}.HasDensity 1 := by
  sorry

/--
Quantitative form of the (negative) answer to `erdos_448`. Erdős and Tenenbaum [ErTe81] showed that
the upper density of $\{n : \tau^+(n) < \epsilon \cdot \tau(n)\}$ is in fact
$\asymp \epsilon^{1 - o(1)}$, where the $o(1)$ in the exponent tends to $0$ as $\epsilon \to 0$.
Equivalently, $\log(\text{upper density}) / \log \epsilon \to 1$ as $\epsilon \to 0^+$. -/
@[category research solved, AMS 11]
theorem erdos_448.variants.erdos_tenenbaum :
    Tendsto
      (fun ε : ℝ =>
        Real.log ({n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}.upperDensity) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  sorry

/--
A more precise result of Hall and Tenenbaum [HaTe88, §4.6]: the upper density of
$\{n : \tau^+(n) < \epsilon \cdot \tau(n)\}$ is $\ll \epsilon \cdot \log(2/\epsilon)$ as
$\epsilon \to 0^+$. -/
@[category research solved, AMS 11]
theorem erdos_448.variants.hall_tenenbaum_upper_bound :
    (fun ε : ℝ => ({n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}).upperDensity)
      =O[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ε * Real.log (2 / ε)) := by
  sorry

/--
Hall and Tenenbaum [HaTe88] further prove that $\tau^+(n)/\tau(n)$ has a distribution function:
there is a function `F` such that, for every $z$, the set $\{n : \tau^+(n)/\tau(n) \le z\}$ has
density `F z`. -/
@[category research solved, AMS 11]
theorem erdos_448.variants.hall_tenenbaum_distribution :
    ∃ F : ℝ → ℝ, ∀ z : ℝ,
      {n : ℕ | (tauPlus n : ℝ) / (n.divisors.card : ℝ) ≤ z}.HasDensity (F z) := by
  sorry

/--
Erdős and Graham asked whether there is a good inequality for $\sum_{n \le x} \tau^+(n)$. This was
answered by Ford [Fo08], who proved
$$ \sum_{n \le x} \tau^+(n) \asymp x \cdot \frac{(\log x)^{1 - \alpha}}{(\log\log x)^{3/2}}, $$
where $\alpha = 1 - \frac{1 + \log\log 2}{\log 2} = 0.08607\ldots$. -/
@[category research solved, AMS 11]
theorem erdos_448.variants.ford :
    (fun x : ℕ => ∑ n ∈ Finset.Icc 1 x, (tauPlus n : ℝ))
      =Θ[atTop]
      (fun x : ℕ =>
        let α : ℝ := 1 - (1 + Real.log (Real.log 2)) / Real.log 2
        (x : ℝ) * Real.log (x : ℝ) ^ (1 - α)
          / Real.log (Real.log (x : ℝ)) ^ ((3 : ℝ) / 2)) := by
  sorry

end Erdos448
