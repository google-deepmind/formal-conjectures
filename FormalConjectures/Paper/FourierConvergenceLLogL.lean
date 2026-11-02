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
# Almost everywhere convergence of Fourier series in `L log L`

Do the symmetric Fourier partial sums of every function in `L log L` on the circle converge
almost everywhere? Carleson proved almost everywhere convergence in `L²` [Ca66] and Hunt in `Lᵖ`
for `p > 1` [Hu68], while Kolmogorov constructed an integrable function whose Fourier series
diverges almost everywhere [Ko23]. Antonov proved convergence in `L log L log log log L` [An96].
Lie formulates the `L log L` question through a weak-`L¹` maximal bound
[Li17, Definition 1.1 and Conjecture 1].

*References:*
- [An96] N. Yu. Antonov, *Convergence of Fourier series*, East J. Approx. 2 (1996), 187–196.
- [Ca66] L. Carleson, *On convergence and growth of partial sums of Fourier series*, Acta Math.
  116 (1966), 135–157.
- [Hu68] R. A. Hunt, *On the convergence of Fourier series*, in *Orthogonal expansions and their
  continuous analogues*, Southern Illinois Univ. Press (1968), 235–255.
- [Ko23] A. Kolmogoroff, *Une série de Fourier–Lebesgue divergente presque partout*, Fund. Math.
  4 (1923), 324–328.
- [Li17] V. Lie, *Pointwise convergence of Fourier series (I). On a conjecture of Konyagin*,
  J. Eur. Math. Soc. 19 (2017), 1655–1728.
- [OAI26] OpenAI, *Almost-everywhere Fourier convergence in L log L*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/Almost-everywhere-Fourier-convergence-in-L-log-L-September-23-2026/paper.pdf
-/

@[expose] public section

open MeasureTheory Filter Topology AddCircle

namespace FourierConvergenceLLogL

local instance circlePeriod_pos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The symmetric Fourier partial sum `S_N f x = ∑_{|k| ≤ N} f̂(k) e^{ikx}` on
`𝕋 = ℝ / 2πℤ`. -/
noncomputable def partialSum (f : AddCircle (2 * Real.pi) → ℂ) (N : ℕ)
    (x : AddCircle (2 * Real.pi)) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f k * fourier k x

/--
**Fourier series converge almost everywhere in `L log L`.** If `f : 𝕋 → ℂ` is measurable and
`∫ |f| log (2 + |f|) < ∞`, then `S_N f x → f x` for almost every `x`.

This was proved by an internal OpenAI model in September 2026 [OAI26].
-/
@[category research solved, AMS 42]
theorem fourier_convergence_l_log_l : ∀ f : AddCircle (2 * Real.pi) → ℂ,
    AEStronglyMeasurable f haarAddCircle →
    Integrable (fun x ↦ ‖f x‖ * Real.log (2 + ‖f x‖)) haarAddCircle →
    ∀ᵐ x ∂haarAddCircle, Tendsto (fun N ↦ partialSum f N x) atTop (𝓝 (f x)) := by
  sorry

/-- **Carleson.** Fourier series of functions in `L²` converge almost everywhere [Ca66]. -/
@[category research solved, AMS 42]
theorem fourier_convergence_l_log_l.variants.carleson : ∀ f : AddCircle (2 * Real.pi) → ℂ,
    MemLp f 2 haarAddCircle →
    ∀ᵐ x ∂haarAddCircle, Tendsto (fun N ↦ partialSum f N x) atTop (𝓝 (f x)) := by
  sorry

/-- **Hunt.** Fourier series of functions in `Lᵖ`, `p > 1`, converge almost everywhere [Hu68]. -/
@[category research solved, AMS 42]
theorem fourier_convergence_l_log_l.variants.hunt (p : ENNReal) (hp : 1 < p) :
    ∀ f : AddCircle (2 * Real.pi) → ℂ, MemLp f p haarAddCircle →
    ∀ᵐ x ∂haarAddCircle, Tendsto (fun N ↦ partialSum f N x) atTop (𝓝 (f x)) := by
  sorry

/-- **Kolmogorov.** Some integrable function has a Fourier series that diverges almost
everywhere [Ko23], so `L log L` cannot be replaced by `L¹`. -/
@[category research solved, AMS 42]
theorem fourier_convergence_l_log_l.variants.kolmogorov : ∃ f : AddCircle (2 * Real.pi) → ℂ,
    Integrable f haarAddCircle ∧
    ∀ᵐ x ∂haarAddCircle, ¬ ∃ l, Tendsto (fun N ↦ partialSum f N x) atTop (𝓝 l) := by
  sorry

/-- `L²` functions are in `L log L`, so the main statement implies Carleson's theorem. -/
@[category test, AMS 42]
theorem carleson_of_fourier_convergence_l_log_l (h : type_of% fourier_convergence_l_log_l) :
    type_of% fourier_convergence_l_log_l.variants.carleson := by
  intro f hf
  have hm := hf.1
  refine h f hm (Integrable.mono' ((hf.integrable one_le_two).norm.add
    ((memLp_two_iff_integrable_sq_norm hm).1 hf)) ?_ (Eventually.of_forall fun x => ?_))
  · exact (hm.norm.aemeasurable.mul
      (aemeasurable_const.add hm.norm.aemeasurable).log).aestronglyMeasurable
  · have ht : 0 ≤ ‖f x‖ := norm_nonneg _
    have hlog0 : 0 ≤ Real.log (2 + ‖f x‖) := Real.log_nonneg (by linarith)
    have hlog : Real.log (2 + ‖f x‖) ≤ 1 + ‖f x‖ := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < 2 + ‖f x‖ by linarith)]
    rw [Real.norm_of_nonneg (mul_nonneg ht hlog0), Pi.add_apply]
    nlinarith

end FourierConvergenceLLogL
