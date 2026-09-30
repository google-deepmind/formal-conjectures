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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 243

*Reference:* [erdosproblems.com/243](https://www.erdosproblems.com/243)
-/

@[expose] public section

open Filter

open scoped Topology

namespace Erdos243

/--
Let $a_1 < a_2 < \dots$ be a sequence of integers such that
$\lim_{n\to\infty} \frac{a_n}{a_{n-1}^2} = 1$ and $\sum \frac{1}{a_n} \in \mathbb{Q}$.

Then, for all sufficiently large $n \ge 1$, $a_n = a_{n-1}^2 - a_{n-1} + 1$.
-/
@[category research open, AMS 40]
theorem erdos_243 (a : ℕ → ℕ) (ha₀ : StrictMono a)
    (ha₁ : Tendsto (fun n ↦ (a n : ℝ) / a (n - 1) ^ 2) atTop (𝓝 1))
    (ha₂ : Summable ((1 : ℚ) / a ·)) :
      ∀ᶠ n in atTop, a n = a (n - 1) ^ 2 - a (n - 1) + 1 := by
  sorry

open scoped BigOperators

namespace erdos_243.variants

/-- The prefix product of a positive integer sequence. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

/-- The increment of the prefix-product ratio, expressed using consecutive terms. -/
noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)

/-- The truncated base-two iterated logarithm. -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2

/--
The slow-growth clause of Cook's theorem on bounded or slowly growing increments
of the product ratio: a rational reciprocal sum and quadratic growth force
an eventual Sylvester recurrence if the product defect has this extra bound.
See the [slow-growth clause of Theorem `long243:res:strausbounded`](https://github.com/wcook04/plectis-erdos/blob/40008384cb6e343c5a93841701ecc25b97974141/paper/reasoning-parts/erdos243/core.tex#L2307-L2320)
in Cook’s long Erdős 243 paper. The related Erdős–Straus criterion
([Theorem 3, p. 132](https://users.renyi.hu/~p_erdos/1964-19.pdf))
uses an LCM prefactor rather than this prefix-product hypothesis.
This sufficient condition leaves the unrestricted parent open.
-/
@[category research solved, AMS 11 40, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos-lean/blob/d1be0b5416aa58e84f7bcd72c961c525f24e4910/Solutions/PalomarCorpus/E243_06/PaperStatementsL.lean#L65-L77"]
theorem slow_growth_product_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (δ : ℝ) (hδ : 0 < δ)
    (hslow : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productDefect a n ≤ (1 - δ) / (q : ℝ) *
        recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ))) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry

end erdos_243.variants

/--
Let $(a_n)_{n\geq 0}$ be a strictly increasing sequence of positive integers. If
$$
  \frac{a_n^2}{a_{n+1}}=1+\frac{3}{n}+o(n^{-3}),
$$
then its reciprocal sum is irrational.

This is the zero-indexed formal version of [Theorem 7.2 (PDF p. 12)](https://raw.githubusercontent.com/wcook04/plectis-erdos/7ab6a901a2fe07e8d0e5c99dc46821adffc7411b/paper/243/erdos-243-reciprocal-tail-rigidity.pdf#page=12)
in Will Cook, *Cubic-Rate Irrationality and Reciprocal-Tail Rigidity*. The
[rounded recurrence beginning at $a_1=8$ (PDF p. 13)](https://raw.githubusercontent.com/wcook04/plectis-erdos/7ab6a901a2fe07e8d0e5c99dc46821adffc7411b/paper/243/erdos-243-reciprocal-tail-rigidity.pdf#page=13)
is an example satisfying the rate. The rate keeps the same index on both sides;
shifting $n$ would change its lower-order terms.
This variant does not settle the unrestricted Erdős problem above.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos/blob/a1779f508dbede5da6d8c2d5fefe0d8f6dcef6d9/research/adapters/FC243CubicRate.lean#L53-L60"]
theorem erdos_243.variants.cubic_rate (a : ℕ → ℕ)
    (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ)))) atTop (𝓝 0)) :
    Irrational (∑' n : ℕ, 1 / (a n : ℝ)) := by
  sorry

end Erdos243
