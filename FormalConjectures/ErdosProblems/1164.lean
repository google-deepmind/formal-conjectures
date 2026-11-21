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
public import FormalConjectures.ErdosProblems.«1165»

/-!
# Erdős Problem 1164

*References:*
- [erdosproblems.com/1164](https://www.erdosproblems.com/1164)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
- [ErTa60] Erdős, P. and Taylor, S. J., *Some problems concerning the structure of random walk
  paths*. Acta Math. Acad. Sci. Hungar. 11 (1960), 137--162.
  [PDF](https://www.renyi.hu/~p_erdos/1960-17.pdf)
- [Re90] Révész, P., *Random walk in random and non-random environments*. World Scientific,
  Singapore (1990).
- [DPRZ04] Dembo, A., Peres, Y., Rosen, J. and Zeitouni, O., *Cover times for Brownian motion and
  random walks in two dimensions*. Ann. of Math. (2) 160 (2004), 433--464.
  [arXiv:math/0107191](https://arxiv.org/abs/math/0107191)
-/

@[expose] public section

open MeasureTheory Filter
open scoped ProbabilityTheory Topology

namespace Erdos1164

open Erdos1165

/-- `Covers X n ω S` says that the walk has visited every site of `S` by time `n`: each `x ∈ S`
equals `position X k ω` for some `k ≤ n`. The visit at time `0` counts. -/
def Covers {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) (S : Set (ℤ × ℤ)) : Prop :=
  ∀ x ∈ S, ∃ k ≤ n, position X k ω = x

/-- The sites `x = (a, b)` of $\mathbb{Z}^2$ with Euclidean norm $\lVert x\rVert\leq r$. The
condition is written without a square root as $a^2+b^2\leq r^2$. -/
def closedDisc (r : ℕ) : Set (ℤ × ℤ) :=
  {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 ≤ (r : ℤ) ^ 2}

/-- The sites `x = (a, b)` of $\mathbb{Z}^2$ with Euclidean norm $\lVert x\rVert<r$. This is the
disc $D_r=D(0,r)\cap\mathbb{Z}^2$ of [DPRZ04, Section 5]. -/
def openDisc (r : ℕ) : Set (ℤ × ℤ) :=
  {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 < (r : ℤ) ^ 2}

/-- `coveringRadius X n ω` is the largest integer `r` such that, by time `n`, the walk has visited
every site `x` with $\lVert x\rVert\leq r$. This is the radius $R_n$ of the problem, which depends
on the walk `ω`.

The set of such `r` contains `0`, since the origin is visited at time `0`. It is bounded: the
sites $(j,0)$ with $\lvert j\rvert\leq r$ are $2r+1$ different sites visited at times at most
`n`, so $2r\leq n$. Hence `sSup` is a maximum and there is no junk value. -/
noncomputable def coveringRadius {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) : ℕ :=
  sSup {r : ℕ | Covers X n ω (closedDisc r)}

/-- The disc of radius `0` is covered at every time, because the origin is visited at time `0`. -/
@[category API, AMS 60]
theorem covers_closedDisc_zero {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) :
    Covers X n ω (closedDisc 0) := by
  intro x hx
  have hx' : x.1 ^ 2 + x.2 ^ 2 ≤ ((0 : ℕ) : ℤ) ^ 2 := hx
  rw [Nat.cast_zero] at hx'
  have h1 : x.1 ^ 2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have h2 : x.2 ^ 2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  refine ⟨0, Nat.zero_le n, ?_⟩
  rw [position_zero]
  exact Prod.ext ((pow_eq_zero_iff two_ne_zero).1 h1).symm
    ((pow_eq_zero_iff two_ne_zero).1 h2).symm

/--
Let $R_n$ be the maximal integer such that almost every random walk from the origin in
$\mathbb{Z}^2$ visits every $x\in\mathbb{Z}^2$ with $\lVert x\rVert\leq R_n$ in at most $n$ steps.

Is it true that
$$\log R_n \asymp \sqrt{\log n}?$$

A problem of Erdős and Taylor, see [ErTa60, p. 153] and [Va99, 6.76]. This is true, as proved
independently by Révész [Re90] and Kesten, see [DPRZ04, Section 1.3], which reports that they
proved the following. The probability that the disc of radius $n$ is covered by time
$e^{t(\log n)^2}$ has $\liminf_{n\to\infty}$ at least $e^{-b/t}$ and $\limsup_{n\to\infty}$ at
most $e^{-a/t}$ for every $t>0$, where $0<a<b<\infty$ are constants. The exact limit is in
`erdos_1164.variants.dembo_peres_rosen_zeitouni`.

We take the simple random walk (`IsSimpleRandomWalkSteps`). Read literally, $R_n$ would be $0$:
for every $n$ some walk misses a neighbour of the origin, and such walks have positive
probability. So $R_n=R_n(\omega)$ is the random variable `coveringRadius`, and
$\log R_n\asymp\sqrt{\log n}$ means tightness: for every $\varepsilon>0$ there are constants
$c>0$ and $C$ such that $c\sqrt{\log n}\leq\log R_n\leq C\sqrt{\log n}$ with probability at least
$1-\varepsilon$ for all large $n$. This is the sense of the results above and of
`erdos_1164.variants.dembo_peres_rosen_zeitouni`, which are about probabilities, not almost sure
bounds. [ErTa60, p. 153] asks an almost sure question about the time needed to cover the disc of
radius $n$; we follow the results in probability reported in [DPRZ04, Section 1.3].
-/
@[category research solved, question, AMS 60]
theorem erdos_1164 {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ ε : ℝ, 0 < ε → ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ (ℙ {ω | c * Real.sqrt (Real.log n) ≤ Real.log (coveringRadius X n ω) ∧
        Real.log (coveringRadius X n ω) ≤ C * Real.sqrt (Real.log n)}).toReal := by
  sorry

/--
Dembo, Peres, Rosen and Zeitouni [DPRZ04, Theorem 1.4] proved a conjecture of Kesten and Révész:
if $T_n$ is the time it takes the simple random walk in $\mathbb{Z}^2$ to cover the disc of
radius $n$, then
$$\lim_{n\to\infty}\mathbb{P}\left(\log T_n\leq t(\log n)^2\right)=e^{-4/t}$$
for every $t>0$.

The disc is $D_n=D(0,n)\cap\mathbb{Z}^2$ (`openDisc`). Since $T_n$ is an integer,
$\log T_n\leq t(\log n)^2$ holds if and only if $T_n\leq\lfloor e^{t(\log n)^2}\rfloor$, that is,
if the disc is covered by that time.
-/
@[category research solved, AMS 60]
theorem erdos_1164.variants.dembo_peres_rosen_zeitouni {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦
      (ℙ {ω | Covers X ⌊Real.exp (t * Real.log n ^ 2)⌋₊ ω (openDisc n)}).toReal)
      atTop (𝓝 (Real.exp (-4 / t))) := by
  sorry

end Erdos1164
