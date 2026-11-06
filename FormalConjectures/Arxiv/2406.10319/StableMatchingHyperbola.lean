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
# Pittel's stable-matching hyperbola threshold conjecture

*Reference:*
[On Constrained Matchings, Stable Under Random Preferences](https://doi.org/10.1002/rsa.70036)
by Boris Pittel, Section 6, Notes (2).
The conjecture also appears in the [arXiv preprint, p. 26](https://arxiv.org/pdf/2406.10319#page=26).
-/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped Topology

namespace Arxiv.«2406.10319»

/-- The joint law of the uniform preference profile and the independent admissibility mask. -/
noncomputable def marketLaw (n : ℕ) (p : unitInterval) : Measure (Profile n × Admissibility n) :=
  (uniformProfile n).toMeasure.prod (Admissibility.law n p)

/-- The rank products are within $\varepsilon$ of $1$ after scaling both ranks by $\sqrt{pn^3}$,
and the scaled pairs cover the arc $(t,t^{-1})$ for $t \in [2/3,3/2]$ to that tolerance in each
coordinate. The event is empty when $n=0$ or $p=0$, where the scale vanishes. -/
def hyperbolaEvent (n : ℕ) (p : unitInterval) (ε : ℝ) : Set (Profile n × Admissibility n) :=
  {ω |
    let s := Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3)
    let q (M : PartialMatching n) := (totalWifeRank ω.1 ω.2 M : ℝ) / s
    let r (M : PartialMatching n) := (totalHusbandRank ω.1 ω.2 M : ℝ) / s
    0 < n ∧ 0 < (p : ℝ) ∧
      (∀ M, IsPartialStable ω.1 ω.2 M → |q M * r M - 1| ≤ ε) ∧
      ∀ t ∈ Set.Icc (2 / 3 : ℝ) (3 / 2), ∃ M, IsPartialStable ω.1 ω.2 M ∧
        max |q M - t| |r M - t⁻¹| ≤ ε}

/-- Pittel conjectures a threshold $p_*(n)$ for the rank pairs across stable matchings to trace
out a hyperbola. For all sufficiently large $n$, it lies between $\frac{9}{4}(\log n)^2/n$ and $1$.

This formulation uses the fixed arc with $t \in [2/3,3/2]$ in `hyperbolaEvent` and the
relative margin $\delta\min(p_*(n),1-p_*(n))$ for each fixed $0<\delta<1$. Above the threshold by
at least this margin, the event holds with high probability uniformly for every positive tolerance.
Below the threshold by at least this margin, it fails with high probability uniformly at a positive
tolerance that may depend on $\delta$. -/
@[category research open, AMS 5 60]
theorem pittel_hyperbola_threshold :
    ∃ pStar : ℕ → Set.Ioo (0 : ℝ) 1,
      let d (n : ℕ) := min (pStar n : ℝ) (1 - (pStar n : ℝ))
      (∀ᶠ (n : ℕ) in atTop, (9 / 4 : ℝ) * (Real.log n) ^ 2 / n < (pStar n : ℝ)) ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        (∀ ε > 0, Tendsto (fun n ↦
          ⨆ p : {p : unitInterval // (pStar n : ℝ) + δ * d n ≤ (p : ℝ)},
            marketLaw n p.1 (hyperbolaEvent n p.1 ε)ᶜ) atTop (𝓝 0)) ∧
        ∃ ε > 0, Tendsto (fun n ↦
          ⨆ p : {p : unitInterval // (p : ℝ) ≤ (pStar n : ℝ) - δ * d n},
            marketLaw n p.1 (hyperbolaEvent n p.1 ε)) atTop (𝓝 0) := by
  sorry

end Arxiv.«2406.10319»
