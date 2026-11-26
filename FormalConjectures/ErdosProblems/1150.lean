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
# Erdős Problem 1150

*References:*
- [erdosproblems.com/1150](https://www.erdosproblems.com/1150)
- [OAI26a] OpenAI, *Asymptotically minimal maxima of real Littlewood polynomials*. OpenAI Math
  Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Asymptotically-minimal-maxima-of-real-Littlewood-polynomials-September-23-2026/paper.pdf
-/

@[expose] public section

open scoped Polynomial

namespace Erdos1150

set_option linter.style.formal_proof_palomar false in
/--
Is there some constant $c > 0$ such that, for all large enough $n$ and all polynomials $P$ of
degree $n$ with coefficients in $\{-1, 1\}$,
$$\max_{|z|=1} |P(z)| > (1 + c) \sqrt{n}?$$

No. This was disproved by an internal OpenAI model in September 2026 [OAI26a]; see the linked
Lean proof. It proves `erdos_1150.variants.signs`, which implies this statement by
`erdos_1150_of_signs`.
-/
@[category research solved, question, AMS 12 30, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Littlewood/Main.lean#L187"]
theorem erdos_1150 :
    ¬ ∃ c > 0, ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],  (∀ i ≤ P.natDegree, P.coeff i = - 1 ∨ P.coeff i = 1) → P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n := by
  sorry

/--
The form of `erdos_1150` proved in [OAI26a]: for every $\eta > 0$ and every large $N$, there are
signs $\varepsilon_0, \ldots, \varepsilon_{N-1} \in \{-1, 1\}$ with
$\lvert \sum_{k<N} \varepsilon_k z^k\rvert \le (1 + \eta)\sqrt{N}$ for all $\lvert z\rvert = 1$.
Here $N$ is the number of coefficients, so the polynomial has degree $N - 1$.
-/
@[category research solved, AMS 12 30]
theorem erdos_1150.variants.signs :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ ε : Fin N → ℝ, (∀ k, ε k = -1 ∨ ε k = 1) ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)‖ ≤ (1 + η) * Real.sqrt N := by
  sorry

/--
`erdos_1150.variants.signs` implies `erdos_1150`. Given $c > 0$, take $\eta = c / 2$ and
$N = n + 1$. For large $n$, $(1 + c/2)\sqrt{n + 1} \le (1 + c)\sqrt{n}$.
-/
@[category test, AMS 12 30]
theorem erdos_1150_of_signs (h : type_of% erdos_1150.variants.signs) :
    type_of% erdos_1150 := by
  rintro ⟨c, hc, hev⟩
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨N₀, -, hN₀⟩ := h (c / 2) (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_gt ((1 + c / 2) ^ 2 / (c + 3 * c ^ 2 / 4))
  set n := max (max M N₀) K
  have hMn : M ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have hN₀n : N₀ ≤ n + 1 := ((le_max_right _ _).trans (le_max_left _ _)).trans n.le_succ
  have hKn : (K : ℝ) ≤ n := by exact_mod_cast le_max_right _ _
  obtain ⟨ε, hε, hbound⟩ := hN₀ (n + 1) hN₀n
  set P : ℂ[X] := ∑ k : Fin (n + 1), Polynomial.C (ε k : ℂ) * Polynomial.X ^ (k : ℕ) with hP
  have hcoeff (i : ℕ) (hi : i ≤ n) : P.coeff i = ε ⟨i, Nat.lt_succ_of_le hi⟩ := by
    rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single ⟨i, Nat.lt_succ_of_le hi⟩]
    · simp
    · intro k _ hk
      rw [Polynomial.coeff_C_mul_X_pow, if_neg fun h => hk (Fin.ext h.symm)]
    · simp
  have hpm (i : ℕ) (hi : i ≤ n) : P.coeff i = -1 ∨ P.coeff i = 1 := by
    rw [hcoeff i hi]
    rcases hε ⟨i, Nat.lt_succ_of_le hi⟩ with h | h <;> simp [h]
  have hdeg : P.natDegree = n := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ =>
        (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp k.2)
    · rcases hpm n le_rfl with h | h <;> simp [h]
  have hgrow : (1 + c / 2) * Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (1 + c) * Real.sqrt n := by
    have hsq : (1 + c / 2) ^ 2 * ((n : ℝ) + 1) ≤ (1 + c) ^ 2 * n := by
      have := (div_lt_iff₀ (by positivity)).mp (hK.trans_le hKn)
      nlinarith
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 + c / 2), ← Real.sqrt_sq (by positivity : 0 ≤ 1 + c),
      ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by push_cast; linarith)
  have : Nonempty (Metric.sphere (0 : ℂ) 1) := ⟨⟨1, by simp⟩⟩
  refine (hM n hMn P (fun i hi => hpm i (hdeg ▸ hi)) hdeg).not_ge (ciSup_le fun z => ?_)
  have hz : ‖(z : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  exact (hbound z hz).trans hgrow

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
