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
# Bugeaud Collection of Conjectures and Open Questions: Lacunary Sequences in Real Number Fields

The following problems were proposed and discussed by Dubickas as Conjecture 2 in [Dub09].

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Dub09] Dubickas, Artūras. "An approximation property of lacunary sequences."
    Israel Journal of Mathematics 170.1 (2009): 95-111.
-/

namespace Bugeaud

open Filter

/--
Problem 10.5 (first part). Let $\mathbb{K}$ be a real number field. Then, for any
$\varepsilon > 0$, there exists a lacunary sequence $(t_n)_{n \ge 1}$ of positive numbers
in $\mathbb{K}$ such that
$$\limsup_{n \to \infty} \{\xi t_n\} \ge 1 - \varepsilon,$$
for any real number $\xi$ not in $\mathbb{K}$.
-/
@[category research open, AMS 11]
theorem problem_10_5 (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
      IsLacunaryReal (fun k => (t k : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ K →
        (1 - ε) ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop := by
  sorry

/--
Problem 10.5 ("moreover" clause). With the same hypotheses as `problem_10_5`, the
sequence $(t_n)$ can be chosen so that, for any real $\xi$ not in $\mathbb{K}$, each
subinterval of $[0, 1]$ of length $\varepsilon$ contains a limit point of the sequence
$(\{\xi t_n\})_{n \ge 1}$. This is strictly stronger than `problem_10_5`: the limsup
bound is the special case at the subinterval $[1 - \varepsilon, 1]$.
-/
@[category research open, AMS 11]
theorem problem_10_5_moreover (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
      IsLacunaryReal (fun k => (t k : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ K → ∀ a, a ∈ Set.Icc (0 : ℝ) (1 - ε) →
        ∃ y ∈ Set.Icc a (a + ε),
          MapClusterPt y atTop (fun n => Int.fract (ξ * (t n : ℝ))) := by
  sorry

/-- The "moreover" form of Problem 10.5 implies the first part: applying the cluster-point
density to the subinterval $[1 - \varepsilon, 1]$ yields the required lower bound on the
limsup. -/
@[category test, AMS 11]
theorem problem_10_5_of_moreover (h : type_of% problem_10_5_moreover) :
    type_of% problem_10_5 := by
  intro K _ ε hε
  obtain ⟨t, hpos, hlac, hξ⟩ := h K hε
  refine ⟨t, hpos, hlac, fun ξ hξK => ?_⟩
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => Int.fract (ξ * (t n : ℝ))) :=
    isBoundedUnder_of ⟨1, fun n => (Int.fract_lt_one (ξ * (t n : ℝ))).le⟩
  by_cases hε1 : ε ≤ 1
  · obtain ⟨y, hy, hcluster⟩ := hξ ξ hξK (1 - ε) ⟨by linarith, le_refl _⟩
    have hb_ge : IsBoundedUnder (· ≥ ·) atTop (fun n => Int.fract (ξ * (t n : ℝ))) :=
      isBoundedUnder_of ⟨0, fun n => Int.fract_nonneg (ξ * (t n : ℝ))⟩
    have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun n => Int.fract (ξ * (t n : ℝ))) :=
      hb_ge.isCoboundedUnder_le
    have hle : y ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop := by
      rw [Filter.le_limsup_iff hcob hb]
      exact fun a ha => MapClusterPt.frequently hcluster (eventually_gt_nhds ha)
    linarith [hy.1]
  · push_neg at hε1
    have h0 : (0 : ℝ) ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop :=
      le_limsup_of_frequently_le
        ((Filter.Eventually.of_forall
          fun n => Int.fract_nonneg (ξ * (t n : ℝ))).frequently) hb
    linarith

end Bugeaud
