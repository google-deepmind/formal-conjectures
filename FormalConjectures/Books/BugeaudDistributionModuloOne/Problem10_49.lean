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
# Bugeaud Collection of Conjectures and Open Questions: Normal in a Base and in Continued Fraction

Problem 10.49 asks for a real number that is normal to a given integer base and whose continued
fraction expansion is normal. It was extracted from Queffélec [Que06]. Scheerer [Sch17] and then
Becher and Yuhjtman [BY19] answered it, in the stronger form that asks for every base at once.

Two notions of normality appear here.

* Normality to base $b$ is simple normality to every power $b^k$, $k \ge 1$, which is Pillai's
  theorem [BY19]. `NormalNumber.IsNormalInBase` is *simple* normality, so it is used here only
  through the powers $b^k$, and `NormalNumber.IsAbsolutelyNormal`, which is simple normality to
  every base $b \ge 2$, is absolute normality on the nose.
* Continued fraction normality is stated as in [Sch17, (1.2)]: the orbit of $x$ under the Gauss
  map equidistributes with respect to the Gauss-Kuzmin measure.

Both [Sch17] and [BY19] produce a *computable* number, and [BY19] computes the first $n$ partial
quotients in $O(n^4)$ operations. Computability and the operation count are not stated below.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Que06] Queffélec, Martine. "Old and new results on normality." Dynamics & Stochastics,
    IMS Lecture Notes Monograph Series 48 (2006): 225-236.
  - [Sch17](https://arxiv.org/abs/1701.07979) Scheerer, Adrian-Maria. "On the continued fraction
    expansion of absolutely normal numbers." arXiv preprint arXiv:1701.07979 (2017).
  - [BY19](https://arxiv.org/abs/1704.03622) Becher, Verónica, and Sergio A. Yuhjtman.
    "On absolutely normal and continued fraction normal numbers."
    International Mathematics Research Notices 2019.19 (2019): 6136-6161.
-/

namespace Bugeaud49

open Filter

/--
The Gauss map $T_G(x) = 1/x \bmod 1$, with $T_G(0) = 0$. Iterating it on $x \in [0, 1)$ shifts
the continued fraction expansion of $x$ by one partial quotient.
-/
noncomputable def gaussMap (x : ℝ) : ℝ := Int.fract x⁻¹

/--
The Gauss-Kuzmin measure of $[\alpha, \beta)$,
$$\mu_G([\alpha, \beta)) = \frac{1}{\log 2} \int_\alpha^\beta \frac{dx}{1 + x}
  = \frac{1}{\log 2} \log \frac{1 + \beta}{1 + \alpha}.$$
-/
noncomputable def gaussKuzmin (α β : ℝ) : ℝ := Real.log ((1 + β) / (1 + α)) / Real.log 2

/--
A real number $x$ is *continued fraction normal* if for all $0 \le \alpha < \beta < 1$ the orbit
of $x$ under the Gauss map visits $[\alpha, \beta)$ with asymptotic frequency
$\mu_G([\alpha, \beta))$ [Sch17, (1.2)]. Equivalently, every block of partial quotients occurs
with the frequency given by the Gauss measure.
-/
noncomputable def IsCFNormal (x : ℝ) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → α < β → β < 1 →
    Tendsto (fun n : ℕ ↦ (((Finset.range n).filter
      fun i ↦ gaussMap^[i] x ∈ Set.Ico α β).card : ℝ) / n) atTop (nhds (gaussKuzmin α β))

/--
A real number $x$ is *normal to base* $b$ if every block of $k$ digits occurs in the base $b$
expansion of $x$ with asymptotic frequency $b^{-k}$. By a theorem of Pillai this is simple
normality to every power $b^k$ with $k \ge 1$ [BY19], which is how it is stated here. Note that
`NormalNumber.IsNormalInBase` alone is simple normality, a strictly weaker condition.
-/
noncomputable def IsNormalToBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → NormalNumber.IsNormalInBase (b ^ k) x

/-- The Gauss-Kuzmin measure of the whole interval $[0, 1)$ is $1$. -/
@[category test, AMS 11 37]
theorem gaussKuzmin_zero_one : gaussKuzmin 0 1 = 1 := by
  rw [gaussKuzmin]
  norm_num

/-- The Gauss map fixes $0$, matching the convention $T_G(0) = 0$. -/
@[category test, AMS 11 37]
theorem gaussMap_zero : gaussMap 0 = 0 := by
  simp [gaussMap]

/-- An absolutely normal number is normal to every individual base, since $b^k \ge 2$. -/
@[category test, AMS 11 37]
theorem isNormalToBase_of_isAbsolutelyNormal {x : ℝ} (hx : NormalNumber.IsAbsolutelyNormal x)
    {b : ℕ} (hb : 2 ≤ b) : IsNormalToBase b x :=
  fun k hk ↦ hx _ (hb.trans (Nat.le_self_pow (by omega) b))

/--
Problem 10.49. For every integer base $b \ge 2$ there is a real number $\xi \in [0, 1)$ that is
normal to base $b$ and whose continued fraction expansion is normal. Posed in [Que06]; answered
by Scheerer [Sch17] and by Becher and Yuhjtman [BY19].

The base is prescribed, so the statement quantifies over $b$ first. The weaker reading, that
some base admits such a number, follows from this one.
-/
@[category research solved, AMS 11 37]
theorem problem_10_49 (b : ℕ) (hb : 2 ≤ b) :
    ∃ ξ ∈ Set.Ico (0 : ℝ) 1, IsNormalToBase b ξ ∧ IsCFNormal ξ := by
  sorry

/--
What Scheerer [Sch17], Theorem 6.1, and Becher and Yuhjtman [BY19], Theorem 1, actually prove:
one real number $\xi \in [0, 1)$ is normal to *every* integer base $b \ge 2$ and continued
fraction normal at the same time. Both numbers are computable, and [BY19] computes the first $n$
partial quotients of theirs in $O(n^4)$ operations.
-/
@[category research solved, AMS 11 37]
theorem problem_10_49.variants.absolutely_normal :
    ∃ ξ ∈ Set.Ico (0 : ℝ) 1, NormalNumber.IsAbsolutelyNormal ξ ∧ IsCFNormal ξ := by
  sorry

/--
The metric backdrop of Problem 10.49, which is why the problem asks for a construction: by the
pointwise ergodic theorem, applied to the maps $x \mapsto bx \bmod 1$ and to the Gauss map,
almost every real number in $[0, 1)$ is absolutely normal and continued fraction normal
[Sch17, Section 1], [BY19].
-/
@[category research solved, AMS 11 37]
theorem problem_10_49.variants.almost_everywhere :
    ∀ᵐ ξ ∂(MeasureTheory.volume.restrict (Set.Ico (0 : ℝ) 1)),
      NormalNumber.IsAbsolutelyNormal ξ ∧ IsCFNormal ξ := by
  sorry

end Bugeaud49
