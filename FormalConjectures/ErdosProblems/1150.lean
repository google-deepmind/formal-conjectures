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

import FormalConjecturesUtil

/-!
# Erdős Problem 1150

*Reference:* [erdosproblems.com/1150](https://www.erdosproblems.com/1150)
-/

open scoped Polynomial

namespace Erdos1150

/--
Is there some constant $c > 0$ such that, for all large enough $n$ and all polynomials $P$ of
degree $n$ with coefficients in $\{-1, 1\}$,
$$\max_{|z|=1} |P(z)| > (1 + c) \sqrt{n}?$$
-/
@[category research open, AMS 12 30]
theorem erdos_1150 :
    answer(sorry) ↔ ∃ c > 0, ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],  (∀ i ≤ P.natDegree, P.coeff i = - 1 ∨ P.coeff i = 1) → P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n := by
  sorry

/--
The trivial lower bound from Parseval's identity: for any polynomial $P$ of degree $n$ with
coefficients in $\{-1, 1\}$, we have $\max_{|z|=1} |P(z)| \geq \sqrt{n+1}$.

This follows from Parseval's identity:
$$\frac{1}{2\pi} \int_0^{2\pi} |P(e^{i\theta})|^2 d\theta = \sum_{k=0}^{n} |a_k|^2 = n+1$$
since each $|a_k|^2 = 1$. The circle average is bounded by the pointwise supremum squared, so
$\max_{|z|=1} |P(z)|^2 \ge n+1$, whence $\max_{|z|=1} |P(z)| \ge \sqrt{n+1}$.
-/
@[category textbook, AMS 12 30]
theorem erdos_1150.variants.parseval_lower_bound (P : ℂ[X]) (n : ℕ)
    (hcoeff : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1)
    (hdeg : P.natDegree = n) :
    ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ ≥ Real.sqrt (n + 1) := by
  set N : ℕ := n + 1 with hN
  -- Each coefficient at index $i \le n$ has norm $1$.
  have hcoeff_norm : ∀ i ∈ Finset.range N, ‖P.coeff i‖ = 1 := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rcases hcoeff i (hdeg ▸ hi') with h | h <;> simp [h]
  -- $P$'s support is exactly $\{0, \dots, n\}$: indices $\le n$ are $\pm 1$, hence nonzero;
  -- indices $> n$ have coefficient $0$ by $P.\text{natDegree} = n$.
  have hsupport : P.support = Finset.range N := by
    ext i
    simp only [Polynomial.mem_support_iff, Finset.mem_range]
    refine ⟨fun hne => ?_, fun hi => ?_⟩
    · by_contra hle
      push Not at hle
      exact hne <| Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · have h1 : ‖P.coeff i‖ = 1 := hcoeff_norm i (Finset.mem_range.mpr hi)
      intro h; simp [h] at h1
  -- Apply upstream Parseval. The LHS sum evaluates to $N = n + 1$.
  have hParseval : Real.circleAverage (fun z ↦ ‖P.eval z‖ ^ 2) 0 1 = (N : ℝ) := by
    rw [← P.sum_sq_norm_coeff_eq_circleAverage, hsupport]
    calc ∑ i ∈ Finset.range N, ‖P.coeff i‖ ^ 2
        = ∑ _i ∈ Finset.range N, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hcoeff_norm i hi, one_pow]
      _ = (N : ℝ) := by simp
  -- Triangle inequality: on the unit sphere, $\|P(z)\| \le N$.
  have hdeg' : P.natDegree < N := by omega
  have htri : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖P.eval z‖ ≤ (N : ℝ) := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    calc ‖P.eval z‖
        = ‖∑ i ∈ Finset.range N, P.coeff i * z ^ i‖ := by
          rw [Polynomial.eval_eq_sum_range' hdeg']
      _ ≤ ∑ i ∈ Finset.range N, ‖P.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range N, ‖P.coeff i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_pow, hz1, one_pow, mul_one]
      _ = ∑ _i ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_congr rfl fun i hi => hcoeff_norm i hi
      _ = (N : ℝ) := by simp
  -- The set of $\|P(z)\|$ over the sphere is bounded above by $N$.
  have hbdd : BddAbove
      (Set.range fun z : Metric.sphere (0 : ℂ) 1 => ‖P.eval (z : ℂ)‖) := by
    refine ⟨(N : ℝ), ?_⟩
    rintro _ ⟨⟨z, hz⟩, rfl⟩
    exact htri z hz
  set S : ℝ := ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ with hSdef
  have hS_nonneg : 0 ≤ S := Real.iSup_nonneg fun _ => norm_nonneg _
  -- Every $\|P(z)\|^2 \le S^2$ on the sphere.
  have hbound_sq : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖P.eval z‖ ^ 2 ≤ S ^ 2 := by
    intro z hz
    have hle : ‖P.eval z‖ ≤ S := le_ciSup_of_le hbdd ⟨z, hz⟩ le_rfl
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  -- $\|P(z)\|^2$ is continuous, hence circle-integrable.
  have hCI : CircleIntegrable (fun z ↦ ‖P.eval z‖ ^ 2) 0 1 :=
    (((P.continuous).norm).pow 2).continuousOn.circleIntegrable zero_le_one
  -- Circle-average $\le S^2$.
  have h_avg_le : Real.circleAverage (fun z ↦ ‖P.eval z‖ ^ 2) 0 1 ≤ S ^ 2 := by
    refine Real.circleAverage_mono_on_of_le_circle hCI ?_
    simpa [abs_one] using hbound_sq
  rw [hParseval] at h_avg_le
  -- $N \le S^2$ with $S \ge 0$, so $\sqrt N \le S$.
  have h_sqrt : Real.sqrt ((N : ℝ)) ≤ S := by
    calc Real.sqrt ((N : ℝ))
        ≤ Real.sqrt (S ^ 2) := Real.sqrt_le_sqrt h_avg_le
      _ = S := Real.sqrt_sq hS_nonneg
  calc Real.sqrt ((n : ℝ) + 1)
      = Real.sqrt ((N : ℝ)) := by push_cast [hN]; ring_nf
    _ ≤ S := h_sqrt

end Erdos1150
