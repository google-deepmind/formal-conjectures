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
# Erdős Problem 1118

*References:*
- [erdosproblems.com/1118](https://www.erdosproblems.com/1118)
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. Proceedings of
  the Symposium on Complex Analysis (Canterbury, 1973), London Math. Soc. Lecture Note Ser. 12
  (1974), 155--180.
- [HaLi18] Hayman, W. K. and Lingham, E. F., *Research problems in function theory*.
  [arXiv:1809.07200](https://arxiv.org/abs/1809.07200) (2018).
- [Ha77] Hansen, L. J., *On the growth of entire functions bounded on large sets*.
  Canad. J. Math. 29 (1977), 1287--1291.
- [Ca77] Camera, G., *On the minimum rate of growth of certain classes of integral and subharmonic
  functions*. PhD thesis, Imperial College, University of London (1977).
- [Go79b] Gol'dberg, A. A., *Sets on which the modulus of an entire function has a lower bound*.
  Sibirsk. Mat. Zh. 20 (1979), 512--518, 691.
-/

@[expose] public section

open MeasureTheory Filter

namespace Erdos1118

/-- The maximum modulus $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$ of `f` on the circle of
radius `r`. For continuous `f` and $r\ge 0$ the circle is compact, so the supremum is a maximum.
For $r<0$ the circle is empty and the value is $0$. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) r, ‖f z‖

/-- The set $E(c)=\{z : \lvert f(z)\rvert>c\}$. -/
def superlevelSet (f : ℂ → ℂ) (c : ℝ) : Set ℂ :=
  {z | c < ‖f z‖}

/-- A constant function `a` has maximum modulus $\lvert a\rvert$ on every circle of radius
$r\ge 0$. -/
@[category test, AMS 30]
theorem maxModulus_const (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    maxModulus (fun _ ↦ a) r = ‖a‖ := by
  have : Nonempty (Metric.sphere (0 : ℂ) r) := (NormedSpace.sphere_nonempty.2 hr).to_subtype
  simp [maxModulus]

/-- The sets $E(c)$ decrease as $c$ increases. -/
@[category API, AMS 30]
theorem superlevelSet_anti {f : ℂ → ℂ} {c c' : ℝ} (h : c ≤ c') :
    superlevelSet f c' ⊆ superlevelSet f c :=
  fun _ hz ↦ lt_of_le_of_lt h hz

/--
Let $f(z)$ be a non-constant entire function such that, for some $c$, the set
$E(c)=\{ z: \lvert f(z)\rvert >c\}$ has finite measure.
What is the minimum growth rate of $f(z)$?

This is Problem 2.40 in [Ha74], where it is attributed to Erdős. Hayman conjectured that
$$\int_0^\infty \frac{r}{\log\log M(r)}\,\mathrm{d}r<\infty,$$
where $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$. This was proved by Camera [Ca77] and by
Gol'dberg [Go79b], see [HaLi18, Update 2.40]. Hansen [Ha77, p. 1287] also states it. We state
this necessary condition; `erdos_1118.variants.best_possible` shows that it cannot be improved, and
the two together answer the question.

Since $f$ is non-constant, $M(r)\to\infty$ and the integrand is positive for large $r$. We read
the integral as a condition at infinity: integrability on $(R,\infty)$ for some $R$.
-/
@[category research solved, AMS 30]
theorem erdos_1118.parts.i (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hnc : ¬ ∃ a : ℂ, ∀ z, f z = a) (c : ℝ) (hc : volume (superlevelSet f c) < ⊤) :
    ∃ R : ℝ, IntegrableOn (fun r : ℝ ↦ r / Real.log (Real.log (maxModulus f r))) (Set.Ioi R) := by
  sorry

/--
Camera [Ca77] also showed that this is best possible, in the following form (see the reading
below): if $\varphi$ is increasing and
$\int^\infty r\,\mathrm{d}r/\varphi(r)<\infty$, then there is an entire function $f$ with
$\log\log M(r,f)<\varphi(r)$ which is bounded outside a set of finite area
[HaLi18, Update 2.40].

[HaLi18] prints the hypothesis as $\int r\,\mathrm{d}r/\varphi(r)=\infty$. This contradicts the
necessity of the integral condition in `erdos_1118.parts.i`, so we read it as convergence. We also
take $f$ non-constant, $\varphi$ positive for large $r$, and the bound for large $r$.
-/
@[category research solved, AMS 30]
theorem erdos_1118.variants.best_possible (φ : ℝ → ℝ) (hφ : Monotone φ)
    (hpos : ∀ᶠ r in atTop, 0 < φ r)
    (hint : ∃ R : ℝ, IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi R)) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (¬ ∃ a : ℂ, ∀ z, f z = a) ∧
      (∃ c : ℝ, volume (superlevelSet f c) < ⊤) ∧
      ∀ᶠ r in atTop, Real.log (Real.log (maxModulus f r)) < φ r := by
  sorry

/--
If $E(c)$ has finite measure then must there exist $c'<c$ such that $E(c')$ has finite measure?

The answer is no, by Gol'dberg [Go79b]. He showed that the set
$T=\{c>0 : \lvert E(c)\rvert<\infty\}$ can be any of $\emptyset$, $(0,\infty)$, $[m,\infty)$ and
$(m,\infty)$ with $0<m<\infty$ (see the zbMATH review Zbl 0416.30024); the case $T=[m,\infty)$
gives the answer. For $c\le 0$ the set $E(c)$ always has infinite measure, so only $c'>0$
matters.
-/
@[category research solved, question, AMS 30]
theorem erdos_1118.parts.ii :
    ¬ ∀ f : ℂ → ℂ, Differentiable ℂ f → (¬ ∃ a : ℂ, ∀ z, f z = a) →
      ∀ c : ℝ, volume (superlevelSet f c) < ⊤ → ∃ c' < c, volume (superlevelSet f c') < ⊤ := by
  sorry

/--
Gol'dberg [Go79b] gave an entire function $f$ for which the area $A(c)$ of $E(c)$ is finite for
some $c$ but not for all $c$ [HaLi18, Update 2.40]. We take $c>0$, since for $c\le 0$ the set
$E(c)$ always has infinite measure.
-/
@[category research solved, AMS 30]
theorem erdos_1118.variants.goldberg_example :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (¬ ∃ a : ℂ, ∀ z, f z = a) ∧
      (∃ c : ℝ, 0 < c ∧ volume (superlevelSet f c) < ⊤) ∧
      ∃ c : ℝ, 0 < c ∧ volume (superlevelSet f c) = ⊤ := by
  sorry

end Erdos1118
