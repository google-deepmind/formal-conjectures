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
# Erdős Problem 1099

*References:*
- [erdosproblems.com/1099](https://www.erdosproblems.com/1099)
- [Er81h] Erdős, P., *Some problems and results on additive and multiplicative number theory*.
  Analytic number theory (Philadelphia, Pa., 1980) (1981), 171-182.
- [Vo84] Vose, Michael D., *Integers with consecutive divisors in small ratio*. J. Number Theory
  (1984), 233-238.
-/

@[expose] public section

open Filter

namespace Erdos1099

/--
For $\alpha>1$ and the divisors $1=d_1<\cdots<d_{\tau(n)}=n$ of $n$,
$$h_\alpha(n) = \sum_i \left( \frac{d_{i+1}}{d_i}-1\right)^\alpha.$$
-/
noncomputable def h (α : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1),
    ((Nat.nth (· ∣ n) (i + 1) : ℝ) / Nat.nth (· ∣ n) i - 1) ^ α

/--
Let $1=d_1<\cdots<d_{\tau(n)}=n$ be the divisors of $n$, and for $\alpha>1$ let
$$h_\alpha(n) = \sum_i \left( \frac{d_{i+1}}{d_i}-1\right)^\alpha.$$
Is it true that
$$\liminf_{n\to \infty}h_\alpha(n) \ll_\alpha 1?$$

Erdős [Er81h] remarks that $n!$ or the least common multiple of $\{1,\ldots,n\}$ would be good
candidates for an infinite sequence of $n$ with $h_\alpha(n)$ bounded.

The $\liminf$ is trivially $\geq 1$, just considering the term $i=1$. A positive answer to the
main question was provided by Vose [Vo84] by constructing a specific sequence. It remains open
whether the two explicit sequences mentioned above satisfy this property.

The statement "$\liminf h_\alpha(n)$ is finite" is formalised as "$h_\alpha(n)\leq C$ for
infinitely many $n$".
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1099.lean#L63"]
theorem erdos_1099 : answer(True) ↔
    ∀ α : ℝ, 1 < α → ∃ C : ℝ, ∃ᶠ n : ℕ in atTop, h α n ≤ C := by
  sorry

/-- Is $h_\alpha(n!)$ bounded? -/
@[category research open, AMS 11]
theorem erdos_1099.variants.factorial : answer(sorry) ↔ ∀ α : ℝ, 1 < α →
    ∃ C : ℝ, ∀ n : ℕ, h α n.factorial ≤ C := by
  sorry

/-- Is $h_\alpha(\mathrm{lcm}(1,\ldots,n))$ bounded? -/
@[category research open, AMS 11]
theorem erdos_1099.variants.lcm : answer(sorry) ↔ ∀ α : ℝ, 1 < α →
    ∃ C : ℝ, ∀ n : ℕ, h α ((Finset.Icc 1 n).lcm id) ≤ C := by
  sorry

/--
Erdős remarks that this problem occurred to him when considering $\sum_i \frac{d_{i+1}}{d_i}$.
It is easy to see that $\sum_{i} \frac{d_{i+1}}{d_i}> \tau(n)+\log n$, and Erdős asked whether
$$\liminf \left(\sum_{i} \frac{d_{i+1}}{d_i}-\tau(n)-\log n\right)<\infty,$$
which follows from the affirmative answer to the main question.
-/
@[category research solved, AMS 11]
theorem erdos_1099.variants.ratio_sum : ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
    ∑ i : Fin (n.divisors.card - 1), ((Nat.nth (· ∣ n) (i + 1) : ℝ) / Nat.nth (· ∣ n) i) -
      n.divisors.card - Real.log n ≤ C := by
  sorry

end Erdos1099
