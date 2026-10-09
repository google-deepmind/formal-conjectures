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
# Erdős Problem 265

*References:*
- [erdosproblems.com/265](https://www.erdosproblems.com/265)
- [KoTa24] Kovač, V. and Tao T., On several irrationality problems for Ahmes series.
  arXiv:2406.17593 (2024).
-/

@[expose] public section

namespace Erdos265

open Filter

/--
A strictly increasing sequence of integers $a_n \geq 2$ such that $\sum \frac{1}{a_n}$ and
$\sum \frac{1}{a_n - 1}$ both converge to rational numbers.

The source allows $a_1 = 1$. We require $2 \leq a_0$ because the term $\frac{1}{a_n - 1}$ is
not defined when $a_n = 1$.
-/
def IsRationalPair (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ 2 ≤ a 0 ∧
    (∃ q : ℚ, HasSum (fun n : ℕ ↦ (1 : ℝ) / (a n : ℝ)) (q : ℝ)) ∧
    ∃ q : ℚ, HasSum (fun n : ℕ ↦ (1 : ℝ) / ((a n : ℝ) - 1)) (q : ℝ)

/--
Let $1\leq a_1<a_2<\cdots$ be an increasing sequence of integers. How fast can $a_n\to \infty$
grow if $\sum\frac{1}{a_n}$ and $\sum\frac{1}{a_n-1}$ are both rational?

The remaining critical question asks whether one can achieve $\limsup a_n^{1/2^n}>1$.
Here this is expressed as $a_n\geq c^{2^n}$ infinitely often for some $c>1$.
The zero-based indexing changes the critical root by a square, preserving this question.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/AItoBit/formal-conjectures/blob/2a18dc351bdf5a45d75c232c79c9f609e177b13d/Erdos265Proof.lean"]
theorem erdos_265 : answer(False) ↔ ∃ a : ℕ → ℕ, IsRationalPair a ∧
    ∃ c : ℝ, 1 < c ∧ ∃ᶠ n : ℕ in atTop, c ^ 2 ^ n ≤ (a n : ℝ) := by
  sorry

/--
Kovač and Tao [KoTa24] proved that such a sequence can grow doubly exponentially: there is a
sequence with $a_n^{1/\beta^n} \to \infty$ for some $\beta > 1$.
-/
@[category research solved, AMS 11]
theorem erdos_265.variants.kovac_tao : ∃ a : ℕ → ℕ, IsRationalPair a ∧
    ∃ β : ℝ, 1 < β ∧ Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ (1 / β ^ n)) atTop atTop := by
  sorry

end Erdos265
