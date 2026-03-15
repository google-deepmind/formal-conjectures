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
# Erdős Problem 446

*Reference:* [erdosproblems.com/446](https://www.erdosproblems.com/446)

Let $\delta(n)$ denote the density of positive integers having a divisor in $(n, 2n)$.
Erdős studied the rate at which $\delta(n) \to 0$ and conjectured that
$\delta_1(n) = o(\delta(n))$, where $\delta_1(n)$ is the density of integers with exactly
one such divisor.

**Related problems:** [#448](https://www.erdosproblems.com/448),
[#692](https://www.erdosproblems.com/692), [#693](https://www.erdosproblems.com/693)

**OEIS:** [A074738](https://oeis.org/A074738)

**Bibliography:**

- [Be34] Besicovitch, A. S., _On the density of certain sequences of integers_.
  Math. Annalen (1934), 336-341.
- [Er35] Erdős, P., _Note on sequences of integers no one of which is divisible by any other_.
  J. London Math. Soc. (1935), 126-128.
- [Er60] Erdős, P., _An asymptotic inequality in the theory of numbers_.
  Vestnik Leningrad. Univ. (1960), 41-49.
- [Er79e] Erdős, P., _Some unconventional problems in number theory_ (1979).
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980).
- [Te84] Tenenbaum, G., _Sur la probabilité qu'un entier possède un diviseur dans un intervalle
  donné_. Compositio Math. (1984), 243-263.
- [Fo08] Ford, K., _The distribution of integers with a divisor in a given interval_.
  Ann. of Math. (2) (2008), 367-433.
- [Ob1] Oberwolfach problem session (1986).
-/

open Filter

open scoped Topology

namespace Erdos446

/--
Count of positive integers $m \le N$ having at least one divisor $d$
in the open interval $(n, 2n)$.
-/
def countWithDivisor (n N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun m =>
    ((Finset.Ioo n (2 * n)).filter (fun d => d ∣ m)).Nonempty)).card

/--
Count of positive integers $m \le N$ having exactly $r$ divisors $d$
in the open interval $(n, 2n)$.
-/
def countWithExactDivisors (r n N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun m =>
    ((Finset.Ioo n (2 * n)).filter (fun d => d ∣ m)).card = r)).card

/--
The constant $\alpha = 1 - \frac{1 + \log(\log 2)}{\log 2} \approx 0.08607$,
appearing in the growth rate of $\delta(n)$.
-/
noncomputable def erdos446Alpha : ℝ := 1 - (1 + Real.log (Real.log 2)) / Real.log 2

/--
Ford's theorem on the growth rate of $\delta(n)$ [Fo08]:

Let $\delta(n)$ denote the natural density of integers which are divisible by some
integer in $(n, 2n)$. Ford determined the exact growth rate:
$$\delta(n) \asymp \frac{1}{(\log n)^\alpha \cdot (\log \log n)^{3/2}}$$
where $\alpha = 1 - \frac{1 + \log \log 2}{\log 2} \approx 0.08607$.

This is formalized as: there exist constants $C_1, C_2 > 0$ such that for all
sufficiently large $n$, the proportion of integers $\le N$ with a divisor in $(n, 2n)$
converges (as $N \to \infty$) to a value $\delta(n)$ satisfying
$$C_1 / f(n) \le \delta(n) \le C_2 / f(n)$$
where $f(n) = (\log n)^\alpha \cdot (\log \log n)^{3/2}$.
-/
@[category research solved, AMS 11]
theorem erdos_446 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
        ∃ δ : ℝ,
          Filter.Tendsto (fun N : ℕ => (countWithDivisor n N : ℝ) / (N : ℝ))
            atTop (nhds δ) ∧
          C₁ / ((Real.log (n : ℝ)) ^ erdos446Alpha *
            (Real.log (Real.log (n : ℝ))) ^ ((3 : ℝ) / 2)) ≤ δ ∧
          δ ≤ C₂ / ((Real.log (n : ℝ)) ^ erdos446Alpha *
            (Real.log (Real.log (n : ℝ))) ^ ((3 : ℝ) / 2)) := by
  sorry

/--
Ford's disproof of $\delta_1(n) = o(\delta(n))$ [Fo08]:

Erdős conjectured that $\delta_1(n) = o(\delta(n))$, where $\delta_1(n)$ is the density of
integers with exactly one divisor in $(n, 2n)$. Ford disproved this, showing more
generally that for each $r \ge 1$, $\delta_r(n) \gg_r \delta(n)$, where $\delta_r(n)$ is the
density of integers with exactly $r$ divisors in $(n, 2n)$.

This is formalized as: for each $r \ge 1$, there exists $c > 0$ such that for all
sufficiently large $n$, the natural density $\delta_r(n)$ satisfies
$\delta_r(n) \ge c \cdot \delta(n)$.
-/
@[category research solved, AMS 11]
theorem erdos_446.variants.disproof :
    ∀ r : ℕ, 0 < r →
      ∃ c : ℝ, 0 < c ∧
        ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
          ∃ δ δ_r : ℝ,
            Filter.Tendsto (fun N : ℕ => (countWithDivisor n N : ℝ) / (N : ℝ))
              atTop (nhds δ) ∧
            Filter.Tendsto (fun N : ℕ => (countWithExactDivisors r n N : ℝ) / (N : ℝ))
              atTop (nhds δ_r) ∧
            δ_r ≥ c * δ := by
  sorry

end Erdos446
