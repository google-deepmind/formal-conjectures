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
# Erdős Problem 967

*References:*
- [erdosproblems.com/967](https://www.erdosproblems.com/967)
- [ErIn64] Erdős, P. and Ingham, A. E., *Arithmetical Tauberian theorems*. Acta Arith. (1964),
  341-356.
- [Yi25] Yip, F., *On a problem of Erdős and Ingham*. arXiv:2512.16528 (2025).
-/

open Filter

open scoped Topology

namespace Erdos967

/-- The summand $\frac{1}{n^{1+it}}$, for a natural number $n$ and $t\in\mathbb{R}$. -/
noncomputable def summand (t : ℝ) (n : ℕ) : ℂ := 1 / (n : ℂ) ^ (1 + t * Complex.I : ℂ)

/--
Let $1<a_1<\cdots$ be a sequence of integers such that $\sum\frac{1}{a_i}<\infty$. Is it true
that, for every $t\in \mathbb{R}$,
\[1+\sum_{k}\frac{1}{a_k^{1+it}}\neq 0?\]

Yip [Yi25] has proved that this is not always true - in fact, for any real $t\neq 0$, there
exists a sequence of integers $1<a_1<\cdots$ such that $\sum \frac{1}{a_i}<\infty$ and
$1+\sum_{k}\frac{1}{a_k^{1+it}}=0$.
-/
@[category research solved, AMS 11 30]
theorem erdos_967 : answer(False) ↔
    ∀ a : ℕ → ℕ, StrictMono a → 1 < a 0 → Summable (fun k : ℕ => 1 / (a k : ℝ)) →
      ∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0 := by
  sorry

/--
Yip [Yi25] has proved that this is not always true - in fact, for any real $t\neq 0$, there
exists a sequence of integers $1<a_1<\cdots$ such that $\sum \frac{1}{a_i}<\infty$ and
$1+\sum_{k}\frac{1}{a_k^{1+it}}=0$.
-/
@[category research solved, AMS 11 30]
theorem erdos_967.variants.yip (t : ℝ) (ht : t ≠ 0) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ 1 < a 0 ∧ Summable (fun k : ℕ => 1 / (a k : ℝ)) ∧
      (1 + (∑' k, summand t (a k)) = 0) := by
  sorry

/--
It remains open whether this is true for every finite sequence of integers.
-/
@[category research open, AMS 11 30]
theorem erdos_967.variants.finite : answer(sorry) ↔
    ∀ A : Finset ℕ, (∀ n ∈ A, 1 < n) → ∀ t : ℝ, 1 + (∑ n ∈ A, summand t n) ≠ 0 := by
  sorry

/--
A question of Erdős and Ingham [ErIn64]. The simplest case they could not decide this question
for was the finite sequence $\{2,3,5\}$.
-/
@[category research open, AMS 11 30]
theorem erdos_967.variants.two_three_five : answer(sorry) ↔
    ∀ t : ℝ, 1 + (∑ n ∈ ({2, 3, 5} : Finset ℕ), summand t n) ≠ 0 := by
  sorry

/--
Their interest in this problem arose from their proof that the statement that there are no such
zeros is equivalent to the fact that, for any non-decreasing $f:\mathbb{R}\to \mathbb{R}_{\geq 0}$
which is bounded on every bounded interval and is $=0$ for $x<1$, the relationship
\[f(x)+\sum_k f(x/a_k)=\left(1+\sum_k \frac{1}{a_k}+o(1)\right)x\]
implies $f(x)=(1+o(1))x$.
-/
@[category research solved, AMS 11 40]
theorem erdos_967.variants.tauberian (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1) := by
  sorry

end Erdos967
