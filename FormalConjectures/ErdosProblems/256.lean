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
# Erdős Problem 256

*References:*
- [erdosproblems.com/256](https://www.erdosproblems.com/256)
- [ErSz59] Erdős, P. and Szekeres, G., *On the product $\prod_{k=1}^{n}(1-z^{a_k})$*. Acad. Serbe
  Sci. Publ. Inst. Math. (1959), 29-34.
- [At61] Atkinson, F. V., *On a problem of Erdős and Szekeres*. Canad. Math. Bull. (1961), 7-12.
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [BeKo96] Belov, A. S. and Konyagin, S. V., *An estimate for the free term of a nonnegative
  trigonometric polynomial with integer coefficients*. Mat. Zametki (1996), 627-629.
- [Od82] Odlyzko, A. M., *Minima of cosine sums and maxima of polynomials on the unit circle*.
  J. London Math. Soc. (2) (1982), 412-420.
- [BoCh18] Bourgain, J. and Chang, Mei-Chu, *On a paper of Erdős and Szekeres*. J. Anal. Math.
  (2018), 253-271.
-/

@[expose] public section

open Polynomial Metric Filter Real

open scoped Asymptotics

namespace Erdos256

/-- The supremum of $\lvert\prod_i (1 - z^{a_i})\rvert$ on the unit circle. -/
noncomputable def supNorm {n : ℕ} (a : Fin n → ℕ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖∏ i, (1 - z ^ a i)‖) '' sphere (0 : ℂ) 1)

/--
$f(n)$ is the largest constant such that
$\max_{|z|=1} \lvert\prod_i (1 - z^{a_i})\rvert \ge f(n)$
for every integers $1 \le a_1 \le \cdots \le a_n$.
-/
noncomputable def f (n : ℕ) : ℝ :=
  sInf {M | ∃ a : Fin n → ℕ, (∀ i, 1 ≤ a i) ∧ Monotone a ∧ M = supNorm a}

/--
The strictly increasing analogue $f^*(n)$: the same infimum, but taken only over
$1 \le a_1 < \cdots < a_n$.
-/
noncomputable def fStar (n : ℕ) : ℝ :=
  sInf {M | ∃ a : Fin n → ℕ, (∀ i, 1 ≤ a i) ∧ StrictMono a ∧ M = supNorm a}

/-- The integer polynomial $\prod_i (1 - X^{a_i})$. -/
noncomputable def prodPoly {n : ℕ} (a : Fin n → ℕ) : ℤ[X] := ∏ i, (1 - X ^ a i)

@[category API, AMS 11 30]
theorem prodPoly_ne_zero {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) : prodPoly a ≠ 0 := by
  rw [prodPoly, Finset.prod_ne_zero_iff]
  intro i _ h
  have := congrArg (fun p ↦ p.coeff 0) h
  have h0 : a i ≠ 0 := by
    have := ha i
    omega
  simp [coeff_one, coeff_X_pow, h0.symm] at this

@[category API, AMS 11 30]
theorem pow_X_sub_one_dvd_prodPoly {n : ℕ} (a : Fin n → ℕ) :
    (X - C 1) ^ n ∣ prodPoly a := by
  have : (X - C 1 : ℤ[X]) ^ n = ∏ _i : Fin n, (X - C 1) := by simp
  rw [prodPoly, this]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ ?_
  have := sub_dvd_pow_sub_pow (X : ℤ[X]) 1 (a i)
  rw [one_pow] at this
  simpa using dvd_neg.mpr this

/-- A nonzero polynomial has at least `signVariations + 1` nonzero coefficients. -/
@[category API, AMS 12]
theorem signVariations_add_one_le_card_support {P : ℤ[X]} (hP : P ≠ 0) :
    P.signVariations + 1 ≤ P.support.card := by
  induction h : P.support.card generalizing P with
  | zero => simp_all
  | succ k ih =>
    by_cases hE : P.eraseLead = 0
    · have := eraseLead_add_monomial_natDegree_leadingCoeff P
      rw [hE, zero_add] at this
      rw [← this, signVariations_monomial]
      omega
    · have h1 := signVariations_le_eraseLead_succ P
      have h2 := ih hE (by rw [card_support_eraseLead, h]; rfl)
      omega

/-- By Descartes' rule of signs, since $1$ is a root of multiplicity at least $n$. -/
@[category API, AMS 11 30]
theorem le_signVariations_prodPoly {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) :
    n ≤ (prodPoly a).signVariations := by
  refine le_trans ?_ (roots_countP_pos_le_signVariations _)
  have h1 : n ≤ (prodPoly a).roots.count 1 := by
    rw [count_roots]
    exact (le_rootMultiplicity_iff (prodPoly_ne_zero a ha)).2 (pow_X_sub_one_dvd_prodPoly a)
  refine h1.trans ?_
  rw [Multiset.count_eq_card_filter_eq, Multiset.countP_eq_card_filter]
  exact Multiset.card_le_card (Multiset.monotone_filter_right _ fun x hx ↦ by simp [← hx])

@[category API, AMS 11 30]
theorem card_support_prodPoly {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) :
    n + 1 ≤ (prodPoly a).support.card := by
  have h1 := le_signVariations_prodPoly a ha
  have h2 := signVariations_add_one_le_card_support (prodPoly_ne_zero a ha)
  omega

@[category API, AMS 11 30]
theorem norm_prod_le_two_pow {n : ℕ} (a : Fin n → ℕ) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    ‖∏ i, (1 - z ^ a i)‖ ≤ 2 ^ n := by
  rw [mem_sphere_zero_iff_norm] at hz
  rw [norm_prod]
  calc
    ∏ i, ‖1 - z ^ a i‖ ≤ ∏ _i : Fin n, (2 : ℝ) := by
      gcongr with i
      calc
        ‖1 - z ^ a i‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ a i‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz]; norm_num
    _ = 2 ^ n := by simp

@[category API, AMS 11 30]
theorem bddAbove_image {n : ℕ} (a : Fin n → ℕ) :
    BddAbove ((fun z : ℂ ↦ ‖∏ i, (1 - z ^ a i)‖) '' sphere (0 : ℂ) 1) := by
  refine ⟨2 ^ n, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact norm_prod_le_two_pow a hz

@[category API, AMS 11 30]
theorem bddBelow_fSet (n : ℕ) :
    BddBelow {M | ∃ a : Fin n → ℕ, (∀ i, 1 ≤ a i) ∧ Monotone a ∧ M = supNorm a} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨a, -, -, rfl⟩
  exact (norm_nonneg _).trans (le_csSup (bddAbove_image a) ⟨1, by simp, rfl⟩)

@[category API, AMS 11 30]
theorem const_one_mem_fSet (n : ℕ) :
    supNorm (fun _ : Fin n ↦ 1) ∈
      {M | ∃ a : Fin n → ℕ, (∀ i, 1 ≤ a i) ∧ Monotone a ∧ M = supNorm a} :=
  ⟨fun _ ↦ 1, fun _ ↦ le_rfl, monotone_const, rfl⟩

/--
Parseval: the mean of $\lvert P\rvert^2$ on the unit circle is the sum of the squares of the
integer coefficients, hence at least the number of nonzero coefficients.
-/
@[category API, AMS 11 30]
theorem circleAverage_ge {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) :
    (n : ℝ) + 1 ≤ circleAverage (fun z : ℂ ↦ ‖∏ i, (1 - z ^ a i)‖ ^ 2) 0 1 := by
  set Q : ℂ[X] := (prodPoly a).map (Int.castRingHom ℂ)
  have hQ : ∀ z : ℂ, Q.eval z = ∏ i, (1 - z ^ a i) := by
    intro z
    simp [Q, prodPoly, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_pow, Polynomial.map_X, eval_prod, eval_sub, eval_one, eval_pow, eval_X]
  have hsupp : Q.support = (prodPoly a).support :=
    support_map_of_injective _ (RingHom.injective_int _)
  simp_rw [← hQ, ← sum_sq_norm_coeff_eq_circleAverage, hsupp]
  calc
    (n : ℝ) + 1 ≤ ∑ _i ∈ (prodPoly a).support, (1 : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast card_support_prodPoly a ha
    _ ≤ _ := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [mem_support_iff] at hi
      simp only [Q, coeff_map, eq_intCast, Complex.norm_intCast]
      have : (1 : ℝ) ≤ |((prodPoly a).coeff i : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hi
      nlinarith [abs_nonneg ((prodPoly a).coeff i : ℝ)]

/--
For every choice of positive integers $a_1,\ldots,a_n$, the supremum of
$\lvert\prod_i (1 - z^{a_i})\rvert$ on the unit circle is at least $\sqrt{n+1}$.
-/
@[category textbook, AMS 11 30]
theorem sqrt_le_supNorm {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) :
    √((n : ℝ) + 1) ≤ supNorm a := by
  have hle : ∀ z ∈ sphere (0 : ℂ) 1, ‖∏ i, (1 - z ^ a i)‖ ≤ supNorm a :=
    fun z hz ↦ le_csSup (bddAbove_image a) ⟨z, hz, rfl⟩
  have h0 : 0 ≤ supNorm a := (norm_nonneg _).trans (hle 1 (by simp))
  have hcont : Continuous (fun z : ℂ ↦ ‖∏ i, (1 - z ^ a i)‖ ^ 2) := by fun_prop
  have havg : circleAverage (fun z : ℂ ↦ ‖∏ i, (1 - z ^ a i)‖ ^ 2) 0 1 ≤ supNorm a ^ 2 := by
    refine circleAverage_mono_on_of_le_circle hcont.continuousOn.circleIntegrable' fun z hz ↦ ?_
    rw [abs_one] at hz
    gcongr
    exact hle z hz
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt ((circleAverage_ge a ha).trans havg)

/-- The trivial upper bound $f(n) \le 2^n$. -/
@[category textbook, AMS 11 30]
theorem f_le_two_pow (n : ℕ) : f n ≤ 2 ^ n := by
  refine (csInf_le (bddBelow_fSet n) (const_one_mem_fSet n)).trans ?_
  refine csSup_le ⟨_, 1, by simp, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  exact norm_prod_le_two_pow _ hz

/-- The lower bound $f(n) \ge \sqrt{n+1}$. -/
@[category textbook, AMS 11 30]
theorem sqrt_le_f (n : ℕ) : √((n : ℝ) + 1) ≤ f n := by
  refine le_csInf ⟨_, const_one_mem_fSet n⟩ ?_
  rintro _ ⟨a, ha, -, rfl⟩
  exact sqrt_le_supNorm a ha

/--
Let $n \ge 1$ and let $f(n)$ be maximal such that for any integers $1 \le a_1 \le \cdots \le a_n$
we have
$$\max_{|z|=1} \left\lvert \prod_i (1 - z^{a_i}) \right\rvert \ge f(n).$$
Is it true that there exists some constant $c > 0$ such that $\log f(n) \gg n^c$?

The answer is no. Belov and Konyagin [BeKo96] proved that $\log f(n) \ll (\log n)^4$.
Estimating $f(n)$ more sharply remains open.
-/
@[category research solved, AMS 11 30]
theorem erdos_256 :
    answer(False) ↔ ∃ c > (0 : ℝ), (fun n ↦ log (f n)) ≫ (fun n ↦ (n : ℝ) ^ c) := by
  sorry

/--
Erdős and Szekeres [ErSz59] proved that $\lim_{n\to\infty} f(n)^{1/n} = 1$.
-/
@[category research solved, AMS 11 30]
theorem erdos_256.variants.nthRoot_tendsto :
    Tendsto (fun n : ℕ ↦ f n ^ (1 / (n : ℝ))) atTop (nhds 1) := by
  sorry

/--
Erdős and Szekeres [ErSz59] proved that $f(n) > \sqrt{2n}$.
-/
@[category research solved, AMS 11 30]
theorem erdos_256.variants.sqrt_two_mul_lt_f (n : ℕ) (hn : 0 < n) :
    √(2 * (n : ℝ)) < f n := by
  sorry

/--
Belov and Konyagin [BeKo96] proved that $\log f(n) \ll (\log n)^4$.
-/
@[category research solved, AMS 11 30]
theorem erdos_256.variants.belov_konyagin :
    (fun n ↦ log (f n)) ≪ (fun n ↦ (log n) ^ 4) := by
  sorry

/--
Atkinson [At61] proved that $\log f(n) \ll n^{1/2} \log n$.
-/
@[category research solved, AMS 11 30]
theorem erdos_256.variants.atkinson :
    (fun n ↦ log (f n)) ≪ (fun n ↦ (n : ℝ) ^ (1 / 2 : ℝ) * log n) := by
  sorry

/--
Odlyzko [Od82] proved that $\log f(n) \ll n^{1/3} (\log n)^{4/3}$.
-/
@[category research solved, AMS 11 30]
theorem erdos_256.variants.odlyzko :
    (fun n ↦ log (f n)) ≪
      (fun n ↦ (n : ℝ) ^ (1 / 3 : ℝ) * (log n) ^ (4 / 3 : ℝ)) := by
  sorry

/--
Bourgain and Chang [BoCh18] proved that
$\log f^*(n) \ll (n \log n)^{1/2} \log\log n$.
-/
@[category research solved, AMS 11 30]
theorem erdos_256.variants.bourgain_chang :
    (fun n ↦ log (fStar n)) ≪
      (fun n ↦ ((n : ℝ) * log n) ^ (1 / 2 : ℝ) * log (log n)) := by
  sorry

end Erdos256
