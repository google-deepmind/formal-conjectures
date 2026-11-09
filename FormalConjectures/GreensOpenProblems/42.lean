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
# Green's Open Problem 42

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.42)
- [CoEl03] Cohn, Henry, and Noam Elkies. "New upper bounds on sphere packings I."
  Annals of Mathematics (2003): 689-714.
- [Vi17] Viazovska, Maryna S. "The sphere packing problem in dimension 8."
  Annals of mathematics (2017): 991-1015.
- [CKM17] Cohn, H., Kumar, A., Miller, S., Radchenko, D., & Viazovska, M. (2017).
  The sphere packing problem in dimension 24. Annals of mathematics, 185(3), 1017-1033.
- [Sa21] Sardari, Naser Talebizadeh. "Higher Fourier interpolation on the plane."
  arXiv preprint arXiv:2102.08753 (2021).
- [OAI26a] OpenAI, *A sharp Fourier certificate for planar circle packing*.
  OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf

-/

@[expose] public section

open Real Complex MeasureTheory
open scoped EuclideanGeometry FourierTransform

namespace Green42

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasureSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The real-valued Fourier transform used in the Cohn--Elkies conditions.
For real radial admissible functions, the complex Fourier transform is expected
to be real-valued; we take `.re` to expose the real scalar used in the inequality.

**Convention:** Mathlib's `𝓕 f w` expands to $\int e^{-2\pi i \langle v, w \rangle} f(v) dv$, which
matches [CoEl03]'s $\hat{f}(t) = \int f(x) e^{-2\pi i \langle x, t \rangle} dx$.
-/
noncomputable def fHat (f : V → ℝ) (t : V) : ℝ :=
  (𝓕 (fun x ↦ (f x : ℂ)) t).re

/--
Definition 2.1 from [CoEl03]: A function is admissible if it is continuous and both the function
and its Fourier transform decay sufficiently fast. Continuity is essential: changing `f` at a
single point leaves `fHat f` unchanged, so without it every positive bound would be achievable.
-/
def CohnElkiesAdmissible (f : V → ℝ) : Prop :=
  Continuous f ∧ ∃ C > 0, ∃ δ > 0,
    (∀ x : V, |f x| ≤ C / (1 + ‖x‖) ^ ((Module.finrank ℝ V : ℝ) + δ)) ∧
    (∀ t : V, |fHat f t| ≤ C / (1 + ‖t‖) ^ ((Module.finrank ℝ V : ℝ) + δ))

/--
The structural rules a function must satisfy to successfully pass through
the Cohn-Elkies scheme and generate *some* valid upper bound.
-/
def SatisfiesCohnElkiesScheme (f : V → ℝ) : Prop :=
  CohnElkiesAdmissible f ∧
  (∀ x y : V, ‖x‖ = ‖y‖ → f x = f y) ∧ -- Radial symmetry
  (∀ x : V, 2 ≤ ‖x‖ → f x ≤ 0) ∧       -- Spatial constraint (minimum distance 2)
  (∀ t : V, 0 ≤ fHat f t) ∧            -- Frequency positivity
  (0 < fHat f 0) ∧                     -- Non-zero frequency at the origin
  (0 < f 0)                            -- Positive value at the origin

/--
The statement that there exists a function in dimension `d` satisfying the Cohn-Elkies
scheme which achieves the center density bound `bound`.
-/
def CohnElkiesOptimal (d : ℕ) (bound : ℝ) : Prop :=
  ∃ f : ℝ^d → ℝ,
    SatisfiesCohnElkiesScheme f ∧
    f 0 / fHat f 0 = bound

set_option linter.style.formal_proof_palomar false in
/--
Can the Cohn-Elkies scheme be used to prove the optimal bound for circle-packings in 2 dimensions?

The answer is "yes". This was proved by an internal OpenAI model in September 2026 [OAI26a]; see
the linked Lean proof, which constructs a radial Schwartz certificate normalised to minimum
distance $1$. It proves `green_42.variants.sharp_certificate`, which implies this statement by
`green_42_of_sharp_certificate`.
-/
@[category research solved, question, AMS 51 52, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/PlanarPacking/Main.lean#L32"]
theorem green_42 :
    CohnElkiesOptimal 2 (Real.sqrt 3 / 6) := by
  sorry

/--
The form of `green_42` proved in [OAI26a]: there is a radial Schwartz function $f$ on
$\mathbb{R}^2$ with $\hat f(0) = 1$, $f(0) = 2/\sqrt{3}$, $\hat f$ real and nonnegative, and
$f(x) \le 0$ for $\lVert x\rVert \ge 1$. This certificate is normalised to minimum distance $1$.
-/
@[category research solved, AMS 51 52]
theorem green_42.variants.sharp_certificate :
    ∃ f : SchwartzMap (ℝ^2) ℝ, (∀ x y : ℝ^2, ‖x‖ = ‖y‖ → f x = f y) ∧
      𝓕 (fun x ↦ (f x : ℂ)) 0 = 1 ∧ f 0 = 2 / Real.sqrt 3 ∧
      (∀ ξ, (𝓕 (fun x ↦ (f x : ℂ)) ξ).im = 0 ∧ 0 ≤ (𝓕 (fun x ↦ (f x : ℂ)) ξ).re) ∧
      ∀ x : ℝ^2, 1 ≤ ‖x‖ → f x ≤ 0 := by
  sorry

/-- A Schwartz function is bounded by $C (1 + \lVert x\rVert)^{-3}$. -/
@[category API, AMS 42 46]
private lemma schwartz_decay {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : SchwartzMap E F) :
    ∃ C > 0, ∀ x, ‖φ x‖ ≤ C / (1 + ‖x‖) ^ 3 := by
  set S := 2 ^ 3 * (Finset.Iic ((3, 0) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ
  refine ⟨|S| + 1, by positivity, fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) le_rfl le_rfl φ x
  rw [norm_iteratedFDeriv_zero] at h
  change (1 + ‖x‖) ^ 3 * ‖φ x‖ ≤ S at h
  rw [le_div_iff₀ (by positivity)]
  nlinarith [le_abs_self S]

/--
`green_42.variants.sharp_certificate` implies `green_42`. If $f$ is the certificate, then
$g(x) = f(x/2)$ is normalised to minimum distance $2$, $\hat g(\xi) = 4 \hat f(2\xi)$, and
$g(0)/\hat g(0) = (2/\sqrt{3})/4 = \sqrt{3}/6$.
-/
@[category test, AMS 51 52]
theorem green_42_of_sharp_certificate (h : type_of% green_42.variants.sharp_certificate) :
    type_of% green_42 := by
  obtain ⟨f, hrad, h0, hf0, hpos, hneg⟩ := h
  have hscale (t : ℝ^2) : 𝓕 (fun x : ℝ^2 ↦ ((f ((2 : ℝ)⁻¹ • x) : ℝ) : ℂ)) t =
      4 * 𝓕 (fun x ↦ (f x : ℂ)) ((2 : ℝ) • t) := by
    rw [fourier_eq', fourier_eq']
    calc ∫ x : ℝ^2, Complex.exp (↑(-2 * π * inner ℝ x t) * Complex.I) •
          ((f ((2 : ℝ)⁻¹ • x) : ℝ) : ℂ)
        = ∫ x : ℝ^2, (fun y : ℝ^2 ↦ Complex.exp (↑(-2 * π * inner ℝ y ((2 : ℝ) • t)) *
            Complex.I) • ((f y : ℝ) : ℂ)) ((2 : ℝ)⁻¹ • x) := by
          congr 1
          ext x
          simp only [real_inner_smul_left, real_inner_smul_right]
          congr 4
          field_simp
      _ = _ := by
          rw [Measure.integral_comp_inv_smul (volume : Measure (ℝ^2)) (fun y : ℝ^2 ↦
            Complex.exp (↑(-2 * π * inner ℝ y ((2 : ℝ) • t)) * Complex.I) • ((f y : ℝ) : ℂ)) 2,
            finrank_euclideanSpace_fin]
          norm_num [smul_eq_mul]
  have hfHat (t : ℝ^2) : fHat (fun x ↦ f ((2 : ℝ)⁻¹ • x)) t =
      4 * (𝓕 (fun x ↦ (f x : ℂ)) ((2 : ℝ) • t)).re := by
    simp [fHat, hscale]
  obtain ⟨C₁, hC₁, hd₁⟩ := schwartz_decay f
  obtain ⟨C₂, hC₂, hd₂⟩ := schwartz_decay (𝓕 (f.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM))
  have he : (Module.finrank ℝ (ℝ^2) : ℝ) + 1 = ((3 : ℕ) : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  refine ⟨fun x ↦ f ((2 : ℝ)⁻¹ • x),
    ⟨⟨f.continuous.comp (continuous_const_smul _), 8 * C₁ + 4 * C₂, by positivity, 1, one_pos,
      fun x ↦ ?_, fun t ↦ ?_⟩, fun x y hxy ↦ hrad _ _ (by simp [norm_smul, hxy]),
      fun x hx ↦ hneg _ ?_, fun t ↦ ?_, ?_, ?_⟩, ?_⟩
  · rw [he, Real.rpow_natCast, le_div_iff₀ (by positivity)]
    have hx := hd₁ ((2 : ℝ)⁻¹ • x)
    rw [norm_smul, Real.norm_eq_abs, le_div_iff₀ (by positivity)] at hx
    norm_num at hx
    have hle : 1 + ‖x‖ ≤ 2 * (1 + ‖x‖ / 2) := by linarith
    have hpow : (1 + ‖x‖) ^ 3 ≤ 8 * (1 + ‖x‖ / 2) ^ 3 := by
      calc (1 + ‖x‖) ^ 3 ≤ (2 * (1 + ‖x‖ / 2)) ^ 3 := by gcongr
        _ = 8 * (1 + ‖x‖ / 2) ^ 3 := by ring
    nlinarith [abs_nonneg (f ((2 : ℝ)⁻¹ • x)), pow_pos (show (0 : ℝ) < 1 + ‖x‖ / 2 by positivity) 3]
  · rw [he, Real.rpow_natCast, hfHat, le_div_iff₀ (by positivity)]
    have ht := hd₂ ((2 : ℝ) • t)
    rw [le_div_iff₀ (by positivity)] at ht
    have hre : |(𝓕 (fun x ↦ (f x : ℂ)) ((2 : ℝ) • t)).re| ≤
        ‖𝓕 (f.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM) ((2 : ℝ) • t)‖ :=
      Complex.abs_re_le_norm _
    have hmono : (1 + ‖t‖) ^ 3 ≤ (1 + ‖(2 : ℝ) • t‖) ^ 3 := by
      gcongr
      rw [norm_smul]; norm_num; linarith [norm_nonneg t]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    nlinarith [abs_nonneg (𝓕 (fun x ↦ (f x : ℂ)) ((2 : ℝ) • t)).re,
      pow_pos (show (0 : ℝ) < 1 + ‖t‖ by positivity) 3]
  · rw [norm_smul]; norm_num; linarith
  · rw [hfHat]; exact mul_nonneg (by norm_num) (hpos _).2
  · rw [hfHat, smul_zero, h0]; norm_num
  · simp only [smul_zero, hf0]; positivity
  · simp only [smul_zero, hf0, hfHat, h0, Complex.one_re]
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hs : 0 < Real.sqrt 3 := by positivity
    field_simp
    nlinarith [h3]

/-- [CoEl03] proved this when $d = 1$. -/
@[category research solved, AMS 51 52]
theorem green_42.variants.dimension_one :
    CohnElkiesOptimal 1 (1 / 2) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- [Vi17] established the case $d = 8$. -/
@[category research solved, AMS 51 52, formal_proof using lean4 at "https://github.com/math-inc/Sphere-Packing-Lean/blob/main/SpherePacking/Dim8/MainTheorem.lean"]
theorem green_42.variants.dimension_eight :
    CohnElkiesOptimal 8 (1 / 16) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- In [CKM17], [Vi17] was adapted to $d = 24$. -/
@[category research solved, AMS 51 52, formal_proof using lean4 at "https://github.com/math-inc/Sphere-Packing-Lean/blob/main/SpherePacking/Dim24/MainTheorem.lean"]
theorem green_42.variants.dimension_twenty_four :
    CohnElkiesOptimal 24 1 := by
  sorry

end Green42
