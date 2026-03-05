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
The problem asked whether, for almost all $\alpha$, the sequence of fractional positions
$f(\alpha n)$ is uniformly distributed in $[0,1)$. Disproved by Schmidt.

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

The conjecture asked whether for almost all $\alpha$, the sequence
$f(\alpha n)$ is uniformly distributed in $[0,1)$. Schmidt showed this is false:
there exists such a sequence for which equidistribution fails on a
set of positive measure.
-/
@[category research solved, AMS 11 28]
theorem erdos_492 : answer(False) ↔
    ∀ (a : ℕ → ℕ), StrictMono a → (∀ i, 0 < a i) →
      Tendsto (fun i => (a (i + 1) : ℝ) / (a i : ℝ)) atTop (nhds 1) →
      ∀ᵐ α ∂(volume : Measure ℝ),
        IsEquidistributed (fun n => fractionalPosition a (α * (n : ℝ))) := by
  sorry

end Erdos492
