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
# Erdős Problem 878

*Reference:* [erdosproblems.com/878](https://www.erdosproblems.com/878)

If $n = \prod p_i^{k_i}$ is the factorisation of $n$ into distinct primes, define
$$f(n) = \sum p_i^{\ell_i}$$
where $\ell_i$ is the largest integer with $p_i^{\ell_i} \le n$. Furthermore, define
$$F(n) = \max \sum_{i=1}^{t} a_i$$
where the max is over all pairwise coprime $a_1, \ldots, a_t \le n$ whose prime
factors are all prime factors of $n$ (where $t = \omega(n)$ is the number of
distinct prime factors of $n$).

Conjectures:
1. For almost all $n$, $f(n) = o(n \log \log n)$.
2. For almost all $n$, $F(n) \gg n \log \log n$.
3. $\max_{n \le x} f(n) \sim \frac{x \log x}{\log \log x}$.
4. For all sufficiently large $x$, $\max_{n \le x} f(n) = \max_{n \le x} F(n)$.
5. $H(x) = \sum_{n < x} \frac{f(n)}{n} \ll x \log \log \log \log x$.

[Er84e] Erdős proved (3) along a subsequence of $x \to \infty$.
[Er84e] Erdős proved $x \log\log\log\log x \ll H(x) \ll x \log\log\log x$.
-/

open Finset BigOperators Real

namespace Erdos878

/-- For each prime $p$ dividing $n$, let $\ell = \lfloor \log_p(n) \rfloor$ be the
largest integer with $p^{\ell} \le n$. Then $f(n) = \sum_{p \mid n} p^{\ell}$. -/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

/-- A valid assignment for $F(n)$: a tuple of $\omega(n)$ natural numbers that are
pairwise coprime, each at most $n$, with all prime factors dividing $n$. -/
def ValidAssignment (n : ℕ) (a : Fin n.primeFactors.card → ℕ) : Prop :=
  (∀ i, a i ≤ n) ∧
  (∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) ∧
  (∀ i, ∀ p : ℕ, Nat.Prime p → p ∣ a i → p ∈ n.primeFactors)

/-- $F(n)$: the maximum of $\sum a_i$ over all valid assignments for $n$. -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {s | ∃ a : Fin n.primeFactors.card → ℕ,
    ValidAssignment n a ∧ s = ∑ i, a i}

/-- $H(x) = \sum_{1 \le n < x} \frac{f(n)}{n}$. -/
noncomputable def H (x : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range x).filter (· ≥ 1), (f n : ℝ) / (n : ℝ)

/--
**Erdős Problem 878, Conjecture (1):** For almost all $n$, $f(n) = o(n \log \log n)$.

For every $\varepsilon > 0$ and $\delta > 0$, for all sufficiently large $x$, the proportion of
$n \le x$ with $f(n) > \varepsilon \cdot n \cdot \log(\log n)$ is less than $\delta$.
-/
@[category research open, AMS 11]
theorem erdos_878 :
    ∀ ε : ℝ, ε > 0 → ∀ δ : ℝ, δ > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      (((Finset.Icc 1 x).filter (fun n =>
        (f n : ℝ) > ε * (n : ℝ) * log (log (n : ℝ)))).card : ℝ) /
        (x : ℝ) < δ := by
  sorry

/--
**Erdős Problem 878, Conjecture (2):** For almost all $n$, $F(n) \gg n \log \log n$.

There exists $C > 0$ such that for every $\delta > 0$, for all sufficiently large $x$, the
proportion of $n \le x$ with $F(n) < C \cdot n \cdot \log(\log n)$ is less than $\delta$.
-/
@[category research open, AMS 11]
theorem erdos_878.variants.F_large_almost_all :
    ∃ C : ℝ, C > 0 ∧ ∀ δ : ℝ, δ > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      (((Finset.Icc 1 x).filter (fun n =>
        (F n : ℝ) < C * (n : ℝ) * log (log (n : ℝ)))).card : ℝ) /
        (x : ℝ) < δ := by
  sorry

/--
**Erdős Problem 878, Conjecture (3):**
$\max_{n \le x} f(n) \sim \frac{x \log x}{\log \log x}$.

For every $\varepsilon > 0$, for all sufficiently large $x$,
$(1 - \varepsilon) \cdot \frac{x \log x}{\log \log x} \le \max_{n \le x} f(n)
\le (1 + \varepsilon) \cdot \frac{x \log x}{\log \log x}$.

Erdős [Er84e] proved this along a subsequence of $x \to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_878.variants.f_max_asymptotic :
    ∀ ε : ℝ, ε > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      let M : ℕ := (Finset.Icc 1 x).sup f
      (1 - ε) * ((x : ℝ) * log (x : ℝ) / log (log (x : ℝ))) ≤ (M : ℝ) ∧
      (M : ℝ) ≤ (1 + ε) * ((x : ℝ) * log (x : ℝ) / log (log (x : ℝ))) := by
  sorry

/--
**Erdős Problem 878, Conjecture (4):** For all sufficiently large $x$,
$\max_{n \le x} f(n) = \max_{n \le x} F(n)$.
-/
@[category research open, AMS 11]
theorem erdos_878.variants.max_f_eq_max_F :
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      (Finset.Icc 1 x).sup f = (Finset.Icc 1 x).sup F := by
  sorry

/--
**Erdős Problem 878, Conjecture (5):** $H(x) \ll x \log \log \log \log x$.

There exists $C > 0$ such that for all sufficiently large $x$,
$H(x) \le C \cdot x \cdot \log(\log(\log(\log(x))))$.

Erdős [Er84e] proved $x \log\log\log\log x \ll H(x) \ll x \log\log\log x$.
-/
@[category research open, AMS 11]
theorem erdos_878.variants.H_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      H x ≤ C * (x : ℝ) * log (log (log (log (x : ℝ)))) := by
  sorry

end Erdos878
