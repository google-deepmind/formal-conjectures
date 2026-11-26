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
# Erdős Problem 1165

*References:*
- [erdosproblems.com/1165](https://www.erdosproblems.com/1165)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
- [HLOZ24] Hao, C., Li, X., Okada, I. and Zheng, Y., *Favorite sites for simple random walk in
  two and more dimensions*. [arXiv:2409.00995](https://arxiv.org/abs/2409.00995) (2024).
- [To01] Tóth, B., *No more than three favorite sites for simple random walk*.
  Ann. Probab. 29 (2001), 484--503.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ProbabilityTheory ENNReal

namespace Erdos1165

/-- The four unit steps $(\pm 1, 0)$ and $(0, \pm 1)$ of the simple random walk on
$\mathbb{Z}^2$. -/
def steps : Set (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- `X k` is the $k$-th step of a simple random walk on $\mathbb{Z}^2$, on the probability space
`Ω`: the steps are random variables, they are independent, and each is uniformly distributed on
`steps`. -/
structure IsSimpleRandomWalkSteps {Ω : Type*} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) : Prop where
  /-- Each step is a random variable. -/
  measurable (k : ℕ) : Measurable (X k)
  /-- The steps are independent. -/
  indep : ProbabilityTheory.iIndepFun X ℙ
  /-- Each step is uniform on `steps`. -/
  isUniform (k : ℕ) : MeasureTheory.pdf.IsUniform (X k) steps ℙ Measure.count

/-- The position $s_n = \sum_{k<n} X_k$ of the walk after $n$ steps, so that $s_0 = 0$. -/
def position {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) : ℤ × ℤ :=
  ∑ k ∈ Finset.range n, X k ω

/-- The local time $f_n(x)=\#\{0\le k\le n : s_k=x\}$ of the site `x` at time `n`. -/
def localTime {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) (x : ℤ × ℤ) : ℕ :=
  ((Finset.range (n + 1)).filter fun k ↦ position X k ω = x).card

/-- The set $F(n)=\{x : f_n(x)=\max_y f_n(y)\}$ of favourite sites at time `n`. It is the set of
sites whose local time is at least that of every site. The local time is $0$ outside the finite
set of visited sites, so the maximum exists and `F(n)` is finite and non-empty. -/
def favouriteSites {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) : Set (ℤ × ℤ) :=
  {x | ∀ y, localTime X n ω y ≤ localTime X n ω x}

/-- The walk starts at the origin. -/
@[category API, AMS 60]
theorem position_zero {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : position X 0 ω = 0 := by
  simp [position]

/-- The walk moves by the next step. -/
@[category API, AMS 60]
theorem position_succ {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) :
    position X (n + 1) ω = position X n ω + X n ω := by
  simp [position, Finset.sum_range_succ]

def erdos_1165.answer (r : ℕ) : ℝ≥0∞ := if r = 3 then 1 else 0

/--
Given a random walk $s_0,s_1,\ldots$ in $\mathbb{Z}^2$, starting at the origin, let $f_n(x)$ count
the number of $0\leq k\leq n$ such that $s_k=x$.

Let
$$F(n)=\{ x: f_n(x) = \max_y f_n(y)\}$$
be the set of 'favourite values'. Find
$$\mathbb{P}(\lvert F(n)\rvert=r\textrm{ infinitely often})$$
for $r\geq 3$.

A problem of Erdős and Révész [Va99, 6.77]. We take the simple random walk, on any probability
space (`IsSimpleRandomWalkSteps`). Hao, Li, Okada and Zheng [HLOZ24, Theorem 1.1] showed that the
probability is $1$ for $r=3$ and $0$ for $r\geq 4$, see `erdos_1165.variants.hao_li_okada_zheng`.
The value of `erdos_1165.answer` for $r<3$ is not used.
-/
@[category research solved, question value, AMS 60]
theorem erdos_1165 {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (r : ℕ) (hr : 3 ≤ r) :
    ℙ {ω | ∃ᶠ n in atTop, (favouriteSites X n ω).encard = (r : ℕ∞)} = erdos_1165.answer r := by
  sorry

/--
Hao, Li, Okada and Zheng [HLOZ24, Theorem 1.1] proved that, for the simple random walk on
$\mathbb{Z}^2$, almost surely
$$\limsup_{n\to\infty} \#K^{(2)}(n) = 3,$$
where $K^{(2)}(n)$ is the set of favourite sites at time $n$. The cardinalities are natural
numbers, so almost surely there are eventually at most three favourite sites, and exactly three
infinitely often. Tóth [To01] proved the corresponding bound for the one-dimensional walk, see
[HLOZ24, Section 1].
-/
@[category research solved, AMS 60]
theorem erdos_1165.variants.hao_li_okada_zheng {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ᵐ ω, limsup (fun n ↦ (favouriteSites X n ω).encard) atTop = 3 := by
  sorry

end Erdos1165
