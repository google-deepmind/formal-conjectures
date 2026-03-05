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
# Erdős Problem 420

*Reference:* [erdosproblems.com/420](https://www.erdosproblems.com/420)

If $\tau(n)$ counts the number of divisors of $n$, define
$$F(f, n) = \frac{\tau((n + \lfloor f(n) \rfloor)!)}{\tau(n!)}$$

Three questions:
1. Is it true that $\lim_{n \to \infty} F((\log n)^C, n) = \infty$ for all sufficiently
   large $C$?
2. Is it true that $F(\log n, n)$ is everywhere dense in $(1, \infty)$?
3. More generally, if $f(n) \leq \log n$ is a monotonic function with $f(n) \to \infty$,
   then is $F(f, n)$ everywhere dense in $(1, \infty)$?

Erdős and Graham note it is easy to show $\lim F(n^{1/2}, n) = \infty$.

[EGIP96] Erdős, P., Graham, R., Ivić, A., and Pomerance, C. proved:
- $\liminf F(c \log n, n) = 1$ for any $c > 0$
- $\lim F(n^{4/9}, n) = \infty$
- if $f(n) = o((\log n)^2)$, then $F(f,n) \sim 1$ for almost all $n$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter

open scoped Topology Real

namespace Erdos420

/-- The ratio $F(f, n) = \tau((n + \lfloor f(n) \rfloor)!) / \tau(n!)$ where $\tau$ counts
divisors. Here $f : \mathbb{N} \to \mathbb{R}$ and $\lfloor f(n) \rfloor_+$ is the natural
number floor of $f(n)$. -/
noncomputable def F (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((Nat.divisors (n + ⌊f n⌋₊).factorial).card : ℝ) /
  ((Nat.divisors n.factorial).card : ℝ)

/--
Erdős Problem 420 (Part 1) [ErGr80, p.83]:

Is it true that $\lim_{n \to \infty} F((\log n)^C, n) = \infty$ for all sufficiently large $C$?
-/
@[category research open, AMS 11]
theorem erdos_420 : answer(sorry) ↔
    ∃ C₀ : ℝ, ∀ C : ℝ, C ≥ C₀ →
      Tendsto (fun n : ℕ => F (fun m => (Real.log (m : ℝ)) ^ C) n)
        atTop atTop := by
  sorry

/--
Erdős Problem 420 (Part 2) [ErGr80, p.83]:

Is it true that $F(\log n, n)$ is everywhere dense in $(1, \infty)$?
That is, for any $1 < a < b$, there are infinitely many $n$ with
$a < F(\log n, n) < b$.
-/
@[category research open, AMS 11]
theorem erdos_420.variants.dense_log : answer(sorry) ↔
    ∀ a b : ℝ, 1 < a → a < b →
      ∃ᶠ n in atTop,
        a < F (fun m => Real.log (m : ℝ)) n ∧
        F (fun m => Real.log (m : ℝ)) n < b := by
  sorry

/--
Erdős Problem 420 (Part 3) [ErGr80, p.83]:

More generally, if $f(n) \leq \log n$ is a monotonic function such that $f(n) \to \infty$
as $n \to \infty$, then is $F(f, n)$ everywhere dense in $(1, \infty)$?
-/
@[category research open, AMS 11]
theorem erdos_420.variants.dense_monotone : answer(sorry) ↔
    ∀ f : ℕ → ℝ, Monotone f →
      (∀ n : ℕ, f n ≤ Real.log (n : ℝ)) →
      Tendsto f atTop atTop →
      ∀ a b : ℝ, 1 < a → a < b →
        ∃ᶠ n in atTop,
          a < F f n ∧ F f n < b := by
  sorry

end Erdos420
