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

open scoped Topology
open Metric Set Filter

/-!
# Bloch and Landau constants

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Bloch%27s_theorem_(complex_analysis))
- [CP96] Chen, H., Gauthier, P. M. "On Bloch’s constant." Journal d’Analyse Mathématique 69 (1996),
  275–291.
- [AG37] Ahlfors, L. V., Grunsky, H. "Über die Blochsche Konstante." Mathematische Zeitschrift 42
  (1937), 671–673.
- [Ya95] Yanagihara, H. "On the locally univalent Bloch constant." Journal d’Analyse Mathématique
  65 (1995), 1–17.
- [Ra43] Rademacher, H. "On the Bloch-Landau Constant."" American Journal of Mathematics 65 (1943),
  387–390.
- [OptimizationConstants](https://teorth.github.io/optimizationproblems/constants/57c.html)
- [Skin2009] Skinner, Brian. The univalent Bloch constant problem. Complex Variables and Elliptic
  Equations 54 (2009), no. 10, 951–955.
- [MathWorld](https://mathworld.wolfram.com/BlochConstant.html)
- [Bhowmik–Sen](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/improved-bloch-and-landau-constants-for-meromorphic-functions/FD465D1F2CEF7E8C62AFF16C3E89B7B4)
-/
namespace Bloch

/-- The **Bloch radius** $B_f$ of a function $f$ is the radius of the largest univalent disk in the
image of the unit disk under $f$. -/
noncomputable def blochRadius (f : ℂ → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ S ⊆ ball 0 1, ∃ x, ball x r ⊆ f '' S ∧ InjOn f S}

@[category API, AMS 30]
lemma zero_le_blochRadius (f : ℂ → ℂ) : 0 ≤ blochRadius f := by
  by_cases! hb : BddAbove {r : ℝ | ∃ S ⊆ ball 0 1, ∃ x, ball x r ⊆ f '' S ∧ InjOn f S}
  · exact le_csSup hb ⟨∅, by simp⟩
  · simp_all [blochRadius]

@[category API, AMS 30]
lemma bddBelow_blochRadius : BddBelow (range blochRadius) :=
  bddBelow_def.2 ⟨0, fun _ ⟨f, hf⟩ => hf ▸ zero_le_blochRadius f⟩

@[category API, AMS 54]
lemma dis_add_radius_le_of_ball_subset_ball {X 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [Nontrivial X] {x y : X} {r d : ℝ} (hpos : 0 < r) (hsub : ball x r ⊆ ball y d) :
    dist x y + r ≤ d := by
  have : Tendsto (fun s => dist x y + s) (𝓝[<] r) (𝓝 (dist x y + r)) :=
      (tendsto_nhds_of_tendsto_nhdsWithin tendsto_id).const_add _
  refine le_of_tendsto this ?_
  filter_upwards [Ioo_mem_nhdsLT hpos] with t ⟨hl, hr⟩
  by_cases! hxy : x = y
  · obtain ⟨v, hv⟩ := exists_ne (0 : X)
    simp_all only [dist_self, zero_add]
    let u := (‖v‖⁻¹ : 𝕜) • v
    have : ‖u‖ = 1 := by apply norm_smul_inv_norm; grind
    calc
    _ = ‖y + (t : 𝕜) • u - y‖ := by simp_all [norm_smul, abs_of_nonneg hl.le]
    _ ≤ d := by
      refine (mem_ball_iff_norm.1 (hsub (mem_ball_iff_norm.2 ?_))).le
      simp_all [norm_smul, abs_of_nonneg hl.le]
  · let u := (‖x - y‖⁻¹ : 𝕜) • (x - y)
    have : ‖u‖ = 1 := by apply norm_smul_inv_norm; grind
    calc
    _ = ‖x - y‖ + t := by simp [NormedAddCommGroup.dist_eq]
    _ = ‖x + (t : 𝕜) • u - y‖ := by
      simp [u, add_sub_right_comm, ← smul_assoc]
      nth_rw 2 [← one_smul 𝕜 (x - y)]
      rw [← add_smul, norm_smul]
      norm_cast
      rw [abs_of_nonneg (by positivity), add_mul, one_mul, mul_assoc, inv_mul_cancel₀ (by aesop),
        mul_one]
    _ ≤ d := by
      refine (mem_ball_iff_norm.1 (hsub (mem_ball_iff_norm.2 ?_))).le
      simp_all [norm_smul, abs_of_nonneg hl.le]

@[category API, AMS 54]
lemma radius_le_of_ball_subset_ball {X 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [Nontrivial X] {x y : X} {r d : ℝ} (hpos : 0 < r)
    (hsub : ball x r ⊆ ball y d) : r ≤ d :=
  trans (by simp) (dis_add_radius_le_of_ball_subset_ball (𝕜 := 𝕜) hpos hsub)

@[category API, AMS 30]
lemma blochRadius_id_eq_one : blochRadius id = 1 := by
  refine IsGreatest.csSup_eq ⟨⟨ball 0 1, Subset.rfl, 0, by simp⟩, fun r ⟨S, hS, x, hx⟩ => ?_⟩
  simp only [image_id] at hx
  by_cases hpos : 0 < r
  · exact radius_le_of_ball_subset_ball (𝕜 := ℝ) hpos (hx.1.trans hS)
  · grind

/-- The **Landau radius** $L_f$ of a function $f$ is the radius of the largest disk in the image of
the unit disk under $f$. -/
noncomputable def landauRadius (f : ℂ → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ x, ball x r ⊆ f '' (ball 0 1)}

/-- The **Bloch constant** $B$ is the infimum of the Bloch radius over all functions holomorphic
in the unit disk such that $f'(0) = 1$. -/
noncomputable def blochConstant : ℝ :=
  iInf (fun f : {f : ℂ → ℂ // DifferentiableOn ℂ f (ball 0 1) ∧ deriv f 0 = 1} => blochRadius f.1)

/-- It is proved in [CP96] that the Bloch constant is bounded below by
$\sqrt{3}/4 + 2 \times 10^{-4}$ -/
@[category research solved, AMS 30]
theorem blochConstant_lower_bound : Real.sqrt 3 / 4 + 2 * 10 ^ (-4 : ℤ) ≤ blochConstant := by
  sorry

/-- It is proved in [AG37] that the Bloch constant is bounded above by
$\frac{1}{\sqrt{1 + \sqrt{3}}}\frac{\Gamma(1/3) \Gamma(11/12)}{\Gamma(1/4)}$$. -/
@[category research solved, AMS 30]
theorem blochConstant_upper_bound :
    blochConstant ≤ Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
    (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3)) := by
  sorry

/-- Ahlfors and Grunsky also conjectured in [AG37] that this upper bound is the precise value of the
Bloch constant. -/
@[category research open, AMS 30]
theorem blochConstant_exact_value :
    blochConstant = Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
    (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3)) := by
  sorry

/-- The **Univalent Bloch constant** $B_u$ is the infimum of the Bloch radius over all univalent
functions in the unit disk such that $f'(0) = 1$. -/
noncomputable def univalentBlochConstant : ℝ :=
  iInf (fun f : {f : ℂ → ℂ // InjOn f (ball 0 1) ∧ DifferentiableOn ℂ f (ball 0 1) ∧
    deriv f 0 = 1} => blochRadius f.1)

/-- It is proved in [Skin2009] that the Univalent Bloch constant is bounded below by $0.5708858$. -/
@[category research solved, AMS 30]
theorem univalentBlochConstant_lower_bound : 0.5708858 ≤ univalentBlochConstant := by
  sorry

/-- The Univalent Bloch constant is trivially bounded above by the Bloch radius of the identity
function, which is $1$. This is the best upper bound we know according to [OptimizationConstants]. -/
@[category research solved, AMS 30]
theorem univalentBlochConstant_upper_bound : univalentBlochConstant ≤ 1 := by
  let I : {f : ℂ → ℂ // InjOn f (ball 0 1) ∧ DifferentiableOn ℂ f (ball 0 1) ∧
    deriv f 0 = 1} := ⟨id, by simp; fun_prop⟩
  rw [← blochRadius_id_eq_one, univalentBlochConstant, ← show I.1 = id from by grind]
  exact ciInf_le (bddBelow_blochRadius.mono (range_comp_subset_range _ _)) I

/-- The **Landau constant** $L$ is the infimum of the Landau radius over all functions holomorphic
in the unit disk such that $f'(0) = 1$. -/
noncomputable def landauConstant : ℝ :=
  iInf (fun f : {f : ℂ → ℂ // DifferentiableOn ℂ f (ball 0 1) ∧ deriv f 0 = 1} => landauRadius f.1)

/-- It is proved in [Ya95] that the Landau constant is bounded below by $0.5 + 10 ^ {-335}$. -/
@[category research solved, AMS 30]
theorem landauConstant_lower_bound : 0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant := by
  sorry

/-- It is proved in [Ra43] that the Landau constant is bounded above by
$\frac{1}{\sqrt{1 + \sqrt{3}}}\frac{\Gamma(1/3) \Gamma(5/6)}{\Gamma(1/6)}$. -/
@[category research solved, AMS 30]
theorem landauConstant_upper_bound :
    landauConstant ≤ Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6) := by
  sorry

/-- In [Ra43], Rademacher says that he strongly believed that this upper bound is the precise value
of the Landau constant. -/
@[category research open, AMS 30]
theorem landauConstant_exact_value :
    landauConstant = Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6) := by
  sorry
  
end Bloch

