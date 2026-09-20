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
# Erdős Problem 526

*References:*
- [erdosproblems.com/526](https://www.erdosproblems.com/526)
- [Er61] Erdős, Paul, _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Dv56] Dvoretzky, Aryeh, _On covering a circle by randomly placed arcs_. Proc. Nat. Acad. Sci.
  U.S.A. (1956), 199-203.
- [Ka59] Kahane, Jean-Pierre, _Sur le recouvrement d'un cercle par des arcs disposés au hasard_.
  C. R. Acad. Sci. Paris (1959), 184-186.
- [Sh72] Shepp, L. A., _Covering the circle with random arcs_. Israel J. Math. (1972), 328-345.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real

namespace Erdos526

/-- The open arc of length `ℓ` centred at `z` on the unit circle `ℝ / ℤ`. -/
def arc (z : UnitAddCircle) (ℓ : ℝ) : Set UnitAddCircle := Metric.ball z (ℓ / 2)

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The random points `X n` of the unit circle are independent and uniformly distributed. -/
structure IsIIDUniform (X : ℕ → Ω → UnitAddCircle) : Prop where
  measurable n : Measurable (X n)
  iIndepFun : iIndepFun X ℙ
  map_eq n : Measure.map (X n) ℙ = AddCircle.haarAddCircle

/-- Shepp's condition on the sequence of lengths `a₀ ≥ a₁ ≥ ⋯`:
$$\sum_{n\geq 1} \frac{e^{a_0+\cdots+a_{n-1}}}{n^2}=\infty.$$
-/
def SheppCondition (a : ℕ → ℝ) : Prop :=
  ¬ Summable fun n : ℕ ↦ exp (∑ k ∈ Finset.range (n + 1), a k) / ((n + 1 : ℕ) : ℝ) ^ 2

/--
Let $a_n\geq 0$ with $a_n\to 0$ and $\sum a_n=\infty$. Find a necessary and sufficient condition
on the $a_n$ such that, if we choose (independently and uniformly) random arcs on the unit
circle of length $a_n$, then all the circle is covered with probability $1$.

Solved by Shepp [Sh72], who showed that (for non-increasing $a_n$) a necessary and sufficient
condition is that
$$\sum_n \frac{e^{a_1+\cdots+a_n}}{n^2}=\infty.$$
Since coverage is invariant under permuting the arcs, this decides the general case by passing
to the non-increasing rearrangement of the $a_n$.
-/
@[category research solved, AMS 60]
theorem erdos_526 (a : ℕ → ℝ) (ha : Antitone a) (h0 : ∀ n, 0 ≤ a n)
    (hlim : Tendsto a atTop (nhds 0)) (hdiv : ¬ Summable a) :
    (∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : ℕ → Ω → UnitAddCircle), IsIIDUniform X →
        ∀ᵐ ω, ∀ x : UnitAddCircle, ∃ n, x ∈ arc (X n ω) (a n)) ↔
      SheppCondition a := by
  sorry

/--
Dvoretzky's formulation of the covering problem [Dv56]: Shepp's condition is also necessary and
sufficient for every point of the circle to be covered by infinitely many of the arcs with
probability $1$.
-/
@[category research solved, AMS 60, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos526.lean#L50"]
theorem erdos_526.variants.infinitely_often (a : ℕ → ℝ) (ha : Antitone a)
    (h0 : ∀ n, 0 ≤ a n) (hlim : Tendsto a atTop (nhds 0)) (hdiv : ¬ Summable a) :
    (∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : ℕ → Ω → UnitAddCircle), IsIIDUniform X →
        ∀ᵐ ω, ∀ N, ∀ x : UnitAddCircle, ∃ n ≥ N, x ∈ arc (X n ω) (a n)) ↔
      SheppCondition a := by
  sorry

/--
It is easy to see that (under the given conditions alone) almost all the circle is covered with
probability $1$.
-/
@[category research solved, AMS 60]
theorem erdos_526.variants.almost_all (a : ℕ → ℝ) (h0 : ∀ n, 0 ≤ a n)
    (hlim : Tendsto a atTop (nhds 0)) (hdiv : ¬ Summable a)
    (X : ℕ → Ω → UnitAddCircle) (hX : IsIIDUniform X) :
    ∀ᵐ ω, ∀ᵐ x : UnitAddCircle, ∃ n, x ∈ arc (X n ω) (a n) := by
  sorry

/--
Kahane [Ka59] showed that $a_n=\frac{1+c}{n}$ with $c>0$ has this property, which Erdős
(unpublished) improved to $a_n=\frac{1}{n}$.
-/
@[category research solved, AMS 60]
theorem erdos_526.variants.one_div (c : ℝ) (hc : 0 ≤ c)
    (X : ℕ → Ω → UnitAddCircle) (hX : IsIIDUniform X) :
    ∀ᵐ ω, ∀ x : UnitAddCircle, ∃ n, x ∈ arc (X n ω) ((1 + c) / (n + 1)) := by
  sorry

/-- Erdős also showed that $a_n=\frac{1-c}{n}$ with $c>0$ does not have this property. -/
@[category research solved, AMS 60]
theorem erdos_526.variants.one_sub_div (c : ℝ) (hc : 0 < c)
    (X : ℕ → Ω → UnitAddCircle) (hX : IsIIDUniform X) :
    ¬ ∀ᵐ ω, ∀ x : UnitAddCircle, ∃ n, x ∈ arc (X n ω) ((1 - c) / (n + 1)) := by
  sorry

end Erdos526
