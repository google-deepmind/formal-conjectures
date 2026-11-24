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
# Small Salem numbers and Boyd's closure conjecture

A real algebraic integer $\tau > 1$ is a *Salem number* (`IsSalem`) when all of its remaining
complex Galois conjugates $z$ satisfy $|z| \le 1$, with $|z| = 1$ attained by some conjugate.
The smallest known example is the real root $\sigma_1 \approx 1.17628$ above $1$ of Lehmer's
degree-$10$ polynomial (`lehmerPolynomial`, introduced by Lehmer `[Le33]` for Mahler's measure
problem)
$$P(X) = X^{10} + X^9 - X^7 - X^6 - X^5 - X^4 - X^3 + X + 1.$$
Whether $\sigma_1$ is minimal among all Salem numbers `[Bo77]` `[Bo02, p. 16]`—and even whether $1$
is not an accumulation point of Salem numbers `[Bo77]`, a special case of
`LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem`—remains open. Raphaël Salem `[Sa45]`
proved that every Pisot number (`IsPisot`) is a limit point of Salem numbers and asked
`[Sa63, p. 31]` whether any other real number is a limit point of Salem numbers; David Boyd
`[Bo77, p. 315]` conjectured the closure statement that the union of Pisot and Salem numbers is
closed in $\mathbb{R}$ (which still permits Salem numbers as limit points; see `[Sm15, §3.1]`).

*References:*
- [Wikipedia: Salem number](https://en.wikipedia.org/wiki/Salem_number)
- [Wikipedia: Pisot number](https://en.wikipedia.org/wiki/Pisot%E2%80%93Vijayaraghavan_number)
- `[Le33]` D. H. Lehmer, *Factorization of certain cyclotomic functions*, Ann. of Math. (2) **34**
  (1933), no. 3, 461–479.
- `[Sa45]` R. Salem, *Power series with integral coefficients*, Duke Math. J. **12** (1945),
  153–172.
- `[Sa63]` R. Salem, *Algebraic Numbers and Fourier Analysis*, Heath Mathematical Monographs,
  Boston, 1963, pp. 30–31.
- `[Bo77]` D. W. Boyd, *Small Salem numbers*, Duke Math. J. **44** (1977), no. 2, 315–328.
- `[Bo02]` P. Borwein, *Computational Excursions in Analysis and Number Theory*, CMS Books in
  Mathematics, Springer, 2002, p. 16.
- `[Sm15]` C. Smyth, *Seventy years of Salem numbers*, Bull. Lond. Math. Soc. **47** (2015),
  no. 3, 379–395.
-/

@[expose] public section

namespace SalemNumber

/-- By the intermediate value theorem on $[1.17, 1.18]$, `lehmerPolynomial` vanishes at a real
point $\sigma_1 \in [1.17, 1.18]$. -/
@[category test, AMS 11]
theorem exists_lehmerPolynomial_root_in_Icc :
    ∃ σ₁ ∈ Set.Icc (1.17 : ℝ) 1.18, Polynomial.aeval σ₁ lehmerPolynomial = 0 := by
  let f : ℝ → ℝ := fun x =>
    x ^ 10 + x ^ 9 - x ^ 7 - x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 + x + 1
  have hcont : ContinuousOn f (Set.Icc (1.17 : ℝ) 1.18) := by fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc (f 1.17) (f 1.18) := by
    simp only [f, Set.mem_Icc]
    constructor <;> norm_num
  rcases intermediate_value_Icc (by norm_num : (1.17 : ℝ) ≤ 1.18) hcont h0 with ⟨σ₁, hmem, hf0⟩
  refine ⟨σ₁, hmem, ?_⟩
  simpa [lehmerPolynomial, f] using hf0

/-- Because `Real.goldenRatio` satisfies `IsPisot`, it fails `IsSalem`. -/
@[category test, AMS 11]
theorem not_isSalem_goldenRatio : ¬ IsSalem Real.goldenRatio :=
  _root_.not_isSalem_goldenRatio

/--
Salem's limit-point theorem `[Sa45]`: every Pisot–Vijayaraghavan number $\theta$ is an accumulation
point in $\mathbb{R}$ of the set of Salem numbers.
-/
@[category research solved, AMS 11]
theorem isPisot_accPt_salem {θ : ℝ} (hθ : IsPisot θ) :
    AccPt θ (Filter.principal {τ : ℝ | IsSalem τ}) := by
  sorry

/--
Smallest Salem number conjecture `[Bo77]` `[Bo02, p. 16]`: a real root $\sigma_1 > 1$ of
`lehmerPolynomial` (introduced by Lehmer `[Le33, p. 476]` in studying minimal Mahler measures,
prior to Salem's `[Sa45]` definition of Salem numbers) is minimal among all Salem numbers.
-/
@[category research open, AMS 11]
theorem lehmer_salem_number_conjecture :
    ∃ σ₁ : ℝ, 1 < σ₁ ∧ Polynomial.aeval σ₁ lehmerPolynomial = 0 ∧
      IsLeast {τ : ℝ | IsSalem τ} σ₁ := by
  sorry

/--
Weak Salem conjecture `[Bo77]`: Salem numbers are bounded away from $1$, i.e., there exists
$\delta > 0$ with $\tau \ge 1 + \delta$ for every Salem number $\tau$. The name and standalone
formulation follow Boyd `[Bo77]` rather than the cited Wikipedia pages; this statement is a weaker
consequence of `lehmer_salem_number_conjecture` and the Salem-number case of
`LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem`.
-/
@[category research open, AMS 11]
theorem salem_numbers_bounded_away_from_one :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, IsSalem τ → 1 + δ ≤ τ := by
  sorry

/--
Boyd's closure conjecture `[Bo77, p. 315]` (compare `[Sm15, §3.1]`): the union of the set of
Pisot–Vijayaraghavan numbers and the set of Salem numbers is a closed subset of $\mathbb{R}$.
Unlike Salem's question `[Sa63, p. 31]` asking whether every accumulation point of Salem numbers is
a Pisot number, this closure formulation still permits a Salem number to be an accumulation point.
-/
@[category research open, AMS 11]
theorem pisot_union_salem_isClosed_conjecture :
    IsClosed ({θ : ℝ | IsPisot θ} ∪ {τ : ℝ | IsSalem τ}) := by
  sorry

end SalemNumber
