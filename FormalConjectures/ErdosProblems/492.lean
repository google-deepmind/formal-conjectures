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
# Erdős Problem 492

*Reference:* [erdosproblems.com/492](https://www.erdosproblems.com/492)

Let $A = \{a_1 < a_2 < \cdots\} \subseteq \mathbb{N}$ be infinite with $a_{i+1}/a_i \to 1$.
The problem asked whether, for almost all $\alpha > 0$, the sequence of fractional positions
$f(\alpha n)$ is uniformly distributed in $[0,1)$. Disproved by Schmidt.

[LV53] Le Veque, W.J., _On uniform distribution modulo a subdivision_,
  Pacific J. Math. (1953), 757-771.
[DaLe63] Davenport, H., LeVeque, W.J., _Uniform distribution relative to a fixed sequence_,
  Michigan Math. J. (1963), 315-319.
[DaEr63] Davenport, H., Erdős, P., _A theorem on uniform distribution_,
  Magyar Tud. Akad. Mat. Kutató Int. Közl. (1963), 3-11.
[Sc69] Schmidt, W.M., _Irregularities of distribution. IV_, Invent. Math. 7 (1969), 55-82.
-/

open Filter MeasureTheory Finset

namespace Erdos492

attribute [local instance] Classical.propDecidable

/--
A sequence $x : \mathbb{N} \to \mathbb{R}$ is equidistributed in $[0,1)$ if for every subinterval
$[c, d) \subseteq [0,1)$, the proportion of indices $n < N$ with $x(n) \in [c, d)$
converges to $d - c$ as $N \to \infty$.
-/
def IsEquidistributed (x : ℕ → ℝ) : Prop :=
  ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 →
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => c ≤ x n ∧ x n < d)).card : ℝ) / (N : ℝ))
      atTop (nhds (d - c))

/--
Given a strictly increasing sequence $a : \mathbb{N} \to \mathbb{N}$, for $x$ in some interval
$[a(i), a(i+1))$, returns the fractional position
$(x - a(i)) / (a(i+1) - a(i)) \in [0,1)$.
Returns $0$ if $x$ is not in any such interval.
-/
noncomputable def fractionalPosition (a : ℕ → ℕ) (x : ℝ) : ℝ :=
  if h : ∃ i : ℕ, (a i : ℝ) ≤ x ∧ x < (a (i + 1) : ℝ) then
    let i := Nat.find h
    (x - (a i : ℝ)) / ((a (i + 1) : ℝ) - (a i : ℝ))
  else 0

/--
Erdős Problem 492 (disproved by Schmidt [Sc69]):

Let $A = \{a_1 < a_2 < \cdots\} \subseteq \mathbb{N}$ be infinite with $a_{i+1}/a_i \to 1$.
For $x \geq a_1$, define $f(x) = (x - a_i)/(a_{i+1} - a_i) \in [0,1)$
where $a_i \leq x < a_{i+1}$. For example if $A = \mathbb{N}$ then $f(x) = \{x\}$ is
the usual fractional part operator.

The conjecture asked whether for almost all $\alpha > 0$, the sequence
$f(\alpha n)$ is uniformly distributed in $[0,1)$. Schmidt showed this is false:
there exists such a sequence for which equidistribution fails on a
set of positive measure.
-/
@[category research solved, AMS 11 28]
theorem erdos_492 : answer(False) ↔
    ∀ (a : ℕ → ℕ), StrictMono a → (∀ i, 0 < a i) →
      Tendsto (fun i => (a (i + 1) : ℝ) / (a i : ℝ)) atTop (nhds 1) →
      ∀ᵐ α ∂(volume : Measure ℝ).restrict (Set.Ioi 0),
        IsEquidistributed (fun n => fractionalPosition a (α * (n : ℝ))) := by
  sorry

/--
Davenport–LeVeque (1963) [DaLe63]: If $a_{n+1} - a_n$ is monotone and $a_{n+1}/a_n \to 1$,
then for almost all $\alpha > 0$, the sequence $f(\alpha n)$ is equidistributed in $[0,1)$.
This is a positive partial result for Erdős Problem 492 under a monotone-differences hypothesis.
-/
@[category research solved, AMS 11 28]
theorem erdos_492_monotone_differences :
    ∀ (a : ℕ → ℕ), StrictMono a → (∀ i, 0 < a i) →
      Tendsto (fun i => (a (i + 1) : ℝ) / (a i : ℝ)) atTop (nhds 1) →
      Monotone (fun i => a (i + 1) - a i) →
      ∀ᵐ α ∂(volume : Measure ℝ).restrict (Set.Ioi 0),
        IsEquidistributed (fun n => fractionalPosition a (α * (n : ℝ))) := by
  sorry

/--
Davenport–Erdős (1963) [DaEr63]: If $a_n \gg n^{1/2+\varepsilon}$ for some $\varepsilon > 0$
(i.e., $a_n$ grows at least as fast as $n^{1/2+\varepsilon}$), then for almost all $\alpha > 0$,
the sequence $f(\alpha n)$ is equidistributed in $[0,1)$.
This is a positive partial result for Erdős Problem 492 under a growth-rate hypothesis.
-/
@[category research solved, AMS 11 28]
theorem erdos_492_growth_rate :
    ∀ (a : ℕ → ℕ), StrictMono a → (∀ i, 0 < a i) →
      Tendsto (fun i => (a (i + 1) : ℝ) / (a i : ℝ)) atTop (nhds 1) →
      (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C * (n : ℝ) ^ (1/2 + ε) ≤ (a n : ℝ)) →
      ∀ᵐ α ∂(volume : Measure ℝ).restrict (Set.Ioi 0),
        IsEquidistributed (fun n => fractionalPosition a (α * (n : ℝ))) := by
  sorry

end Erdos492
