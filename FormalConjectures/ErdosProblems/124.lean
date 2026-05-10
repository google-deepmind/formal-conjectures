/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 124

*References:*
- [erdosproblems.com/124](https://www.erdosproblems.com/124)
- [BEGL96] Burr, S. A. and Erdős, P. and Graham, R. L. and Li, W. Wen-Ching, Complete sequences of sets of integer powers. Acta Arith. (1996), 133-138.
-/

open Filter
open scoped Pointwise

namespace Erdos124

/-- The set of integers which are the sum of distinct powers `d ^ i` with `i ≥ k`. -/
def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

/--
Let  $3 \le d_1 < d_2 < \dots < d_r$ be integers such that
$$\sum_{1 \le i \le r}\frac 1{d_i - 1} \ge 1.$$
Can all sufficiently large integers be written as a sum of the shape $\sum_i c_ia_i$
where $c_i \in \{0, 1\}$ and $a_i$ has only the digits $0, 1$ when written in base $d_i$?

Conjectured by Erdős [Er97], solved by Boris Alexeev using Aristotle.
-/
@[category research solved, AMS 11]
lemma erdos124.zero : answer(True) ↔
    ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ →
      ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0 := sorry

/--
Let $k \ne 0$ and $3\leq d_1 < d_2 < \cdots < d_r$ be integers of gcd equal to $1$ such that
$$\sum_{1 \le i \le r}\frac 1{d_i - 1} \ge 1.$$
Can all sufficiently large integers be written as a sum of the shape $\sum_i c_ia_i$
where $c_i \in \{0, 1\}$ and $a_i$ is divisible by $d_i ^ k$ and has only the digits $0, 1$ when
written in base $d_i$?

Conjectured by Burr, Erdős, Graham, and Li [BEGL96]
-/
@[category research open, AMS 11]
lemma erdos124.ne_zero : answer(sorry) ↔
    ∀ k ≠ 0, ∀ D : Finset ℕ, (∀ d ∈ D, 3 ≤ d) → 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ → D.gcd id = 1 →
      ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k := by
  sorry

/--
All sufficiently large integers can be written as $a + b + c$ where $a$ has only the digits $0, 1$
in base $3$, $b$ only the digits $0, 1$ in base $4$, $c$ only the digits $0, 1$ in base $7$.

Provee by Burr, Erdős, Graham, and Li [BEGL96]
-/
@[category research solved, AMS 11]
lemma erdos124.ne_zero_three_four_seven {k : ℕ} (hk : k ≠ 0) :
    ∀ᶠ n in atTop,
      n ∈ sumsOfDistinctPowers 3 k + sumsOfDistinctPowers 4 k + sumsOfDistinctPowers 7 k :=
  sorry

/--
Let $3\leq d_1 < d_2 < \cdots < d_r$ be integers such that all sufficiently large integers can be
written as a sum of the shape $\sum_i c_ia_i$ where $c_i \in \{0, 1\}$ and $a_i$ has only the digits
$0, 1$ when written in base $d_i$. Then
$$\sum_{1 \le i \le r}\frac 1{d_i - 1} \ge 1.$$

Reported by Burr, Erdős, Graham, and Li [BEGL96] as an observation of Pomerance
-/
@[category research solved, AMS 11]
lemma erdos124.converse {D : Finset ℕ} (hD₃ : ∀ d ∈ D, 3 ≤ d)
    (h : ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d 0) : 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹ :=
  sorry

/--
For any $\varepsilon > 0$, there exists an infinite sequence $2 \le d_0 < d_1 < \dots$ such
that all sufficiently large integer can be written as $\sum_{i \in I} a_i$ where $a_i$ has only
the digits $0, 1$ when written in base $d_i$,
but $\sum_{i \in I} \frac 1{d_i - 1} \le \varepsilon$.

Proved by Melfi [Me04]
-/
@[category research solved, AMS 11]
lemma erdos124.melfi_construction {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ → ℕ, StrictMono d ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) 0) ∧
        ∑ i ∈ I, a i = n :=
  sorry

end Erdos124
