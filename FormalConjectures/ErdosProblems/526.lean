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
# Erdős Problem 526

*References:*
- [erdosproblems.com/526](https://www.erdosproblems.com/526)
- [Sh72] Shepp, L. A., _Covering the circle with random arcs_.
  Israel J. Math. 11 (1972), 328–345. https://doi.org/10.1007/BF02789327
- The canonical probability model follows the Apache 2.0 formalization at
  https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos526/Core.lean
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos526

/-- Independent uniform centres on the circle of circumference one. -/
noncomputable def sampleMeasure : Measure (ℕ → UnitAddCircle) :=
  Measure.infinitePi fun _ : ℕ ↦ AddCircle.haarAddCircle

instance : IsProbabilityMeasure sampleMeasure := by
  unfold sampleMeasure
  infer_instance

/-- An open arc centred at `z`. For `0 ≤ ℓ < 1`, its normalized length is `ℓ`. -/
def arc (z : UnitAddCircle) (ℓ : ℝ) : Set UnitAddCircle :=
  Metric.ball z (ℓ / 2)

/-- The event that every point belongs to at least one arc. -/
def onceCoverageEvent (a : ℕ → ℝ) : Set (ℕ → UnitAddCircle) :=
  {ω | ∀ x : UnitAddCircle, ∃ n, x ∈ arc (ω n) (a n)}

/-- The event that every point belongs to infinitely many arcs. -/
def fullCoverageEvent (a : ℕ → ℝ) : Set (ℕ → UnitAddCircle) :=
  {ω | ∀ N : ℕ, ∀ x : UnitAddCircle, ∃ n : ℕ, N ≤ n ∧ x ∈ arc (ω n) (a n)}

/-- Shepp's positive series diverges to infinity. -/
def SheppCondition (a : ℕ → ℝ) : Prop :=
  ¬ Summable (fun n : ℕ ↦ Real.exp (∑ k ∈ Finset.range (n + 1), a k) /
    ((n + 1 : ℕ) : ℝ) ^ 2)

/-- A decreasing enumeration, with multiplicity, of the positive lengths. -/
def IsDecreasingRearrangement (a b : ℕ → ℝ) : Prop :=
  Antitone b ∧ ∃ e : ℕ ≃ {n : ℕ // 0 < a n}, ∀ k : ℕ, b k = a (e k : ℕ)

/--
Let $a_n$ be nonincreasing and nonnegative, with $a_n \to 0$ and
$\sum_n a_n=\infty$. Independently and uniformly place open arcs of lengths $a_n$
on the circle of circumference one. Shepp [Sh72] proved that the circle is covered
with probability $1$ if and only if $\sum_{n\geq 1}n^{-2}e^{a_0+\cdots+a_{n-1}}=\infty$.

The restriction $a_n<1$ follows [Sh72]. It excludes arcs that cover the circle
by themselves and invalidate the necessity of the series condition for one-time coverage.
-/
@[category research solved, AMS 60]
theorem erdos_526 (a : ℕ → ℝ) (ha : Antitone a) (h0 : ∀ n, 0 ≤ a n)
    (h1 : ∀ n, a n < 1) (hlim : Tendsto a atTop (𝓝 0)) (hdiv : ¬ Summable a) :
    sampleMeasure (onceCoverageEvent a) = 1 ↔ SheppCondition a := by
  sorry

/--
Dvoretzky's infinitely-often formulation admits arbitrary nonnegative lengths tending
to zero with divergent sum. There is a decreasing rearrangement $b$ of the positive
lengths such that every circle point belongs to infinitely many arcs almost surely
if and only if $\sum_{n\geq 1}n^{-2}e^{b_0+\cdots+b_{n-1}}=\infty$.
-/
@[category research solved, AMS 60, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos526.lean"]
theorem erdos_526.variants.infinitely_often (a : ℕ → ℝ) (h0 : ∀ n, 0 ≤ a n)
    (hlim : Tendsto a atTop (𝓝 0)) (hdiv : ¬ Summable a) :
    ∃ b : ℕ → ℝ, IsDecreasingRearrangement a b ∧
      (sampleMeasure (fullCoverageEvent a) = 1 ↔ SheppCondition b) := by
  sorry

end Erdos526
