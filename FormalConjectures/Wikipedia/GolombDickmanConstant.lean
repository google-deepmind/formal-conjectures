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
# Irrationality of the Golomb–Dickman Constant

The *Golomb–Dickman constant* $\lambda \approx 0.6243299885$ (`A084945`), studied independently by
Karl Dickman (1930) for largest prime factors of integers and Solomon W. Golomb (1964) for longest
cycles in random permutations, admits the logarithmic-integral representation (derived via random
permutations by Shepp and Lloyd 1966 and equated with Dickman's constant by Knuth and Trabb Pardo
1976; see Finch 2003, §5.4)
$$\lambda = \int_0^1 \exp\left(\int_0^x \frac{dt}{\log t}\right) dx$$
and satisfies Dickman's asymptotic mean formula
$$\lambda = \lim_{n \to \infty} \frac{1}{n} \sum_{k=2}^n \frac{\log P_1(k)}{\log k},$$
where $P_1(k)$ (`Nat.maxPrimeFac k`) denotes the greatest prime divisor of $k$. As noted by
Lagarias (2013), whether $\lambda$ is rational or irrational remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Golomb%E2%80%93Dickman_constant)
- [OEIS A084945](https://oeis.org/A084945)
- K. Dickman, *On the frequency of numbers containing prime factors of a certain relative
  magnitude*, Ark. Mat. Astron. Fys. **22A** (1930), 1–14.
- S. W. Golomb, *Random permutations*, Bull. Amer. Math. Soc. **70** (1964), 747.
- L. A. Shepp and S. P. Lloyd, *Ordered cycle lengths in a random permutation*, Trans. Amer. Math.
  Soc. **121** (1966), 340–357.
- D. E. Knuth and L. Trabb Pardo, *Analysis of a simple factorization algorithm*, Theoret. Comput.
  Sci. **3** (1976), no. 3, 321–348.
- S. R. Finch, *Mathematical Constants*, Cambridge Univ. Press, 2003, §5.4, pp. 284–286.
- J. C. Lagarias, *Euler's constant: Euler's work and modern developments*, Bull. Amer. Math. Soc.
  **50** (2013), no. 4, 527–628.
-/

@[expose] public section

namespace GolombDickmanConstant

/-- Inner logarithmic integral $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ for $0 \le x < 1$
(at $t = 0$, Lean's `Real.log 0 = 0` extends $1 / \log t$ continuously by $0$, and the single
endpoint $x = 1$ has measure zero in the outer integral on $[0, 1]$). -/
noncomputable def golombDickmanInner (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, 1 / Real.log t

/-- The Golomb–Dickman constant
$\lambda = \int_0^1 \exp\bigl(\int_0^x \frac{dt}{\log t}\bigr)\,dx$. -/
noncomputable def golombDickmanConstant : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp (golombDickmanInner x)

/-- At $x = 0$, the inner integral `golombDickmanInner 0` vanishes. -/
@[category test, AMS 11]
theorem golombDickmanInner_zero : golombDickmanInner 0 = 0 := by
  simp [golombDickmanInner]

/-- For every $x \in [0, 1]$, `golombDickmanInner x ≤ 0` since $\log t \le 0$ on $[0, 1]$. -/
@[category API, AMS 11]
theorem golombDickmanInner_nonpos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    golombDickmanInner x ≤ 0 := by
  unfold golombDickmanInner
  rw [← neg_nonneg, ← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_nonneg hx0 fun t ht =>
    neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos zero_le_one
      (Real.log_nonpos ht.1 (ht.2.trans hx1)))

/-- Nonnegativity: $0 \le \lambda$. -/
@[category API, AMS 11]
theorem golombDickmanConstant_nonneg : 0 ≤ golombDickmanConstant := by
  unfold golombDickmanConstant
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => (Real.exp_pos _).le)

/-- On $[0, 1]$, the outer integrand satisfies $\exp(\mathrm{li}(x)) \le 1$. -/
@[category API, AMS 11]
theorem exp_golombDickmanInner_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (golombDickmanInner x) ≤ 1 :=
  Real.exp_le_one_iff.mpr (golombDickmanInner_nonpos hx0 hx1)

/--
**Largest Prime Factor Cesàro Mean** (Dickman 1930; Shepp–Lloyd 1966; Knuth–Trabb Pardo 1976;
Finch 2003, §5.4): the Cesàro average of $\log P_1(k) / \log k$ over $2 \le k \le n$, where
$P_1(k)$ (`Nat.maxPrimeFac k`) denotes the largest prime divisor of $k$, converges as
$n \to \infty$ to the Golomb–Dickman constant $\lambda = \int_0^1 \exp(\mathrm{li}(x))\,dx$.
-/
@[category research solved, AMS 11]
theorem dickman_maxPrimeFac_log_ratio_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        (∑ k ∈ Finset.Icc 2 n, Real.log (k.maxPrimeFac : ℝ) / Real.log (k : ℝ)) / (n : ℝ))
      Filter.atTop (nhds golombDickmanConstant) := by
  sorry

/--
Is the Golomb–Dickman constant $\lambda$ irrational (Lagarias 2013)?
-/
@[category research open, question, AMS 11]
theorem golomb_dickman_constant_irrational : Irrational golombDickmanConstant := by
  sorry

end GolombDickmanConstant
