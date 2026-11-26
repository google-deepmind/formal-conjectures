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
# Skewes's Number and Sign Changes of $\pi(x) - \operatorname{li}(x)$

Let $\pi(x)$ count primes up to $x$ and let
$\operatorname{li}(x) = \operatorname{pv} \int_0^x \frac{dt}{\log t}$ (`Real.logIntegral`) denote
the Cauchy principal-value logarithmic integral. John Edensor Littlewood (1914) proved that
$\pi(x) - \operatorname{li}(x)$ reverses sign infinitely often, and Stanley Skewes (1933, 1955)
established the first explicit upper bounds for a crossover point. Analytic zero-free and
explicit-formula bounds show $\pi(x) < \operatorname{li}(x)$ for $2 \le x \le 10^{19}$ (Büthe
2015), while a crossing region near $e^{727.95133} \approx 1.3972 \times 10^{316}$ was located by
Bays–Hudson (2000, below $e^{727.95209}$), Saouter–Demichel (2010, below $e^{727.9513468}$), and
Saouter–Trudgian–Demichel (2015, below $e^{727.95134}$). Determining the least integer $n \ge 2$
with $\pi(n) > \operatorname{li}(n)$—and whether any crossing precedes the $e^{727.95133}$
region—remains open.

*References:*
- [Wikipedia: Skewes's number](https://en.wikipedia.org/wiki/Skewes%27s_number)
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Prime_numbers)
- J. E. Littlewood, *Sur la distribution des nombres premiers*, C. R. Acad. Sci. **158**
  (1914), 1869–1872.
- S. Skewes, *On the difference $\pi(x) - \operatorname{li}(x)$*, J. London Math. Soc. **8**
  (1933), 277–283.
- S. Skewes, *On the difference $\pi(x) - \operatorname{li}(x)$ (II)*, Proc. London Math. Soc. (3)
  **5** (1955), 48–70.
- C. Bays and R. H. Hudson, *A new bound for the smallest $x$ with $\pi(x) > \operatorname{li}(x)$*,
  Math. Comp. **69** (2000), no. 231, 1285–1296.
- Y. Saouter and P. Demichel, *A sharp region where $\pi(x) - \operatorname{li}(x)$ is positive*,
  Math. Comp. **79** (2010), no. 272, 2395–2405.
- Y. Saouter, T. Trudgian, and P. Demichel, *A still sharper region where
  $\pi(x) - \operatorname{li}(x)$ is positive*, Math. Comp. **84** (2015), no. 295, 2433–2446.
- J. Büthe, *An analytic method for bounding $\psi(x)$*, Math. Comp. **87** (2018), no. 312,
  1991–2009 (`arXiv:1511.02032`, 2015).
-/

@[expose] public section

namespace SkewesNumber

set_option linter.style.formal_proof_palomar false in
/--
Littlewood's oscillation theorem (1914): both $\{m \ge 2 \mid \operatorname{li}(m) < \pi(m)\}$ and
$\{n \ge 2 \mid \pi(n) < \operatorname{li}(n)\}$ are infinite.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/ChironTheCentaur/rh-lab-public/blob/7890f31b6124e4bb197fc6a279654a97f89a7839/problems/littlewood_fc/LittlewoodFC/Main.lean#L127"]
theorem littlewood_pi_minus_li_infinite_sign_changes :
    {m : ℕ | 2 ≤ m ∧ Real.logIntegral (m : ℝ) < (Nat.primeCounting m : ℝ)}.Infinite ∧
      {n : ℕ | 2 ≤ n ∧ (Nat.primeCounting n : ℝ) < Real.logIntegral (n : ℝ)}.Infinite := by
  sorry

/--
Unconditional bounds on the first Skewes crossover: $\pi(n) < \operatorname{li}(n)$ holds for every
integer $2 \le n \le 10^{19}$ (Büthe 2015), whereas some integer $2 \le n < e^{727.95134}$
satisfies $\operatorname{li}(n) < \pi(n)$ (Saouter–Trudgian–Demichel 2015, sharpening Bays–Hudson's
$e^{727.95209}$ and Saouter–Demichel's $e^{727.9513468}$).
-/
@[category research solved, AMS 11]
theorem skewes_crossover_known_bounds :
    (∀ n : ℕ, 2 ≤ n → n ≤ 10 ^ 19 → (Nat.primeCounting n : ℝ) < Real.logIntegral (n : ℝ)) ∧
      (∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) < Real.exp (72795134 / 100000) ∧
        Real.logIntegral (n : ℝ) < (Nat.primeCounting n : ℝ)) := by
  sorry

def skewes_number.answer : ℕ := sorry

/--
What is Skewes's number, the smallest integer $n \ge 2$ satisfying
$\pi(n) > \operatorname{li}(n)$? The bound $n \ge 2$ avoids the singularity of $\operatorname{li}$
at $1$ and $0 = \pi(0) = \operatorname{li}(0)$.
-/
@[category research open, question value, AMS 11]
theorem skewes_number :
    IsLeast {n : ℕ | 2 ≤ n ∧ Real.logIntegral (n : ℝ) < (Nat.primeCounting n : ℝ)}
      skewes_number.answer := by
  sorry

/--
Does $\pi(n) \le \operatorname{li}(n)$ hold for every integer $n \ge 2$ below $e^{727.95132}$, so
that no crossover precedes the known crossing region near $e^{727.95133}$? The rounded threshold
$e^{727.95132}$ is a formalization choice lying just below the crossing interval.
-/
@[category research open, question, AMS 11]
theorem skewes_number.variants.no_crossover_below_known_region :
    ∀ n : ℕ, 2 ≤ n → (n : ℝ) < Real.exp (72795132 / 100000) →
      (Nat.primeCounting n : ℝ) ≤ Real.logIntegral (n : ℝ) := by
  sorry

end SkewesNumber
