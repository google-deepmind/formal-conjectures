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
# Hardness of minimax network-experiment risk

This file states the second-moment ($q = 2$) version of Conjecture 2 in V. Kandiros, C. Harshaw,
and F. Sävje, *A Design-Based Minimax Theory for Network Experiments*, arXiv:2608.04909v1,
Section 6, printed page 23 (PDF page 25).

The precise hardness convention is a rational-threshold promise gap. A yes instance has minimax
risk at most the threshold; a no instance has risk strictly above the threshold times the claimed
approximation factor. Graph order and regular degree vary with the input. The exponent parameter
is fixed for each hardness claim.

Source: https://arxiv.org/pdf/2608.04909v1#page=25
-/

@[expose] public section

open Computability ComplexityTheory

namespace NetworkMinimaxHardness

/-- A nonempty labeled simple graph, its regular degree, and a rational risk threshold. -/
abbrev Input := FiniteGraph × ℕ × ℚ

/-- Regular-graph approximation inputs have degree at least two and a positive threshold. -/
def ValidInput (x : Input) : Prop :=
  2 ≤ x.2.1 ∧ (∀ i, x.1.graph.degree i = x.2.1) ∧ 0 < x.2.2

/-- The finite real-valued second-moment minimax risk for the direct treatment effect. -/
noncomputable def risk (G : FiniteGraph) : ℝ :=
  (NetworkExperiment.minimaxRisk G.graph).toReal

/-- The real risk represents the extended minimax value without discarding an infinite value. -/
@[category API, AMS 62]
theorem ofReal_risk (G : FiniteGraph) :
    ENNReal.ofReal (risk G) = NetworkExperiment.minimaxRisk G.graph :=
  ENNReal.ofReal_toReal (NetworkExperiment.minimaxRisk_ne_top G.graph)

/-- The approximation gap is nontrivial for every valid degree. -/
@[category API, AMS 26 68]
theorem one_lt_factor {ε : ℝ} (hε : ε < 1 / 2) {d : ℕ} (hd : 2 ≤ d) :
    1 < (d : ℝ) ^ (1 / 2 - ε) := by
  apply Real.one_lt_rpow
  · exact_mod_cast (by omega : 1 < d)
  · linarith

/-- The gap problem distinguishes risk at most $a$ from risk strictly above
$d^{1/2-\epsilon}a$; inputs between the two thresholds are unpromised. -/
noncomputable def riskGap (ε : ℝ) (hε : ε < 1 / 2) : PromiseProblem Input where
  yes := {x | ValidInput x ∧ risk x.1 ≤ (x.2.2 : ℝ)}
  no := {x | ValidInput x ∧ (x.2.1 : ℝ) ^ (1 / 2 - ε) * (x.2.2 : ℝ) < risk x.1}
  disjoint := Set.disjoint_left.mpr fun x hy hn ↦ by
    have hfactor := (one_lt_factor hε hy.1.1).le
    have ha : 0 ≤ (x.2.2 : ℝ) := by exact_mod_cast hy.1.2.2.le
    have hgap : (x.2.2 : ℝ) ≤ (x.2.1 : ℝ) ^ (1 / 2 - ε) * (x.2.2 : ℝ) := by
      simpa using mul_le_mul_of_nonneg_right hfactor ha
    exact (not_lt_of_ge (hy.2.trans hgap)) hn.2

/-- Conjecture 2, second-moment version: for every fixed $0<\epsilon<1/2$, approximating the
minimax direct-treatment-effect risk on regular graphs within $d^{1/2-\epsilon}$ is NP-hard.
Here NP-hardness uses polynomial-time many-one reductions to the rational-threshold promise gap,
with varying graph order and regular degree $d\ge2$. -/
@[category research open, AMS 62 68]
theorem conjecture_two_second_moment (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2) :
    (riskGap ε hε₁).IsNPHard := by
  sorry

end NetworkMinimaxHardness
