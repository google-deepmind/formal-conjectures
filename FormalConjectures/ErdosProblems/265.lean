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
# Erdős Problem 265

How fast can a sequence of integers grow if both $\sum 1/a_n$ and $\sum 1/(a_n - 1)$
are rational? Erdős conjectured that $a_n^{1/2^n} \to 1$ must hold.

*Reference:* [erdosproblems.com/265](https://www.erdosproblems.com/265)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[Er88c] Erdős, P., _Problems and results on analytic number theory_ (1988).

[KoTa24] Kovač, V. and Tao T., On several irrationality problems for Ahmes series.
arXiv:2406.17593 (2024).
-/

open Filter

namespace Erdos265

/--
Erdős Problem #265 [ErGr80, p.64] [Er88c, p.104]:

Let $1 \le a_1 < a_2 < \cdots$ be a strictly increasing sequence of integers with
$a_n \ge 2$ for all $n$. If both $\sum 1/a_n$ and $\sum 1/(a_n - 1)$ are rational, then
$a_n^{1/2^n} \to 1$ as $n \to \infty$.

Cantor observed that $a_n = \binom{n}{2}$ is such a sequence. Erdős believed that
$a_n^{1/n} \to \infty$ is possible (proved by Kovač–Tao [KoTa24]) but that
$a_n^{1/2^n} \to 1$ is necessary (still open). A folklore result establishes
that $\sum 1/a_n$ is irrational whenever $a_n^{1/2^n} \to \infty$, so such a sequence
cannot grow faster than doubly exponentially. The remaining question is the
precise exponent possible.
-/
@[category research open, AMS 11 40]
theorem erdos_265
    (a : ℕ → ℕ)
    (ha_mono : StrictMono a)
    (ha_ge : ∀ n, 2 ≤ a n)
    (h_sum_rat : ∃ q : ℚ, HasSum (fun n => (1 : ℝ) / (a n : ℝ)) (q : ℝ))
    (h_shifted_sum_rat : ∃ q : ℚ, HasSum (fun n => (1 : ℝ) / ((a n : ℝ) - 1)) (q : ℝ)) :
    Tendsto (fun n => ((a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (n : ℕ)))) atTop (nhds 1) := by
  sorry

/--
Kovač and Tao [KoTa24] proved that there exists a strictly increasing sequence of integers
with $a_n \ge 2$ such that both $\sum 1/a_n$ and $\sum 1/(a_n - 1)$ are rational and
$a_n^{1/n} \to \infty$. This shows the conjectured bound in `erdos_265` is approximately tight.

[KoTa24] Kovač, V. and Tao T., On several irrationality problems for Ahmes series.
         arXiv:2406.17593 (2024).
-/
@[category research solved, AMS 11 40]
theorem erdos_265_kovac_tao :
    ∃ a : ℕ → ℕ,
      StrictMono a ∧
      (∀ n, 2 ≤ a n) ∧
      (∃ q : ℚ, HasSum (fun n => (1 : ℝ) / (a n : ℝ)) (q : ℝ)) ∧
      (∃ q : ℚ, HasSum (fun n => (1 : ℝ) / ((a n : ℝ) - 1)) (q : ℝ)) ∧
      Tendsto (fun n => ((a n : ℝ) ^ ((1 : ℝ) / (n : ℝ)))) atTop atTop := by
  sorry

/--
Can $\limsup a_n^{1/2^n} > 1$ hold for a strictly increasing sequence with $a_n \ge 2$
and both $\sum 1/a_n$ and $\sum 1/(a_n - 1)$ rational? This is the key remaining open
question highlighted on erdosproblems.com. A positive answer would refute `erdos_265`.
-/
@[category research open, AMS 11 40]
theorem erdos_265_limsup :
    answer(sorry) ↔
    ∃ a : ℕ → ℕ,
      StrictMono a ∧
      (∀ n, 2 ≤ a n) ∧
      (∃ q : ℚ, HasSum (fun n => (1 : ℝ) / (a n : ℝ)) (q : ℝ)) ∧
      (∃ q : ℚ, HasSum (fun n => (1 : ℝ) / ((a n : ℝ) - 1)) (q : ℝ)) ∧
      1 < atTop.limsup (fun n => ((a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (n : ℕ)))) := by
  sorry

end Erdos265
