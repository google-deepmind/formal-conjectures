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
public import FormalConjectures.ErdosProblems.«516»

/-!
# Erdős Problem 1115

*References:*
- [erdosproblems.com/1115](https://www.erdosproblems.com/1115)
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. Proceedings of
  the Symposium on Complex Analysis (Canterbury, 1973), London Math. Soc. Lecture Note Ser. 12
  (1974), 155--180.
- [HaLi18] Hayman, W. K. and Lingham, E. F., *Research problems in function theory*.
  [arXiv:1809.07200](https://arxiv.org/abs/1809.07200) (2018).
- [GoEr79] Gol'dberg, A. A. and Erëmenko, A. È., *On asymptotic curves of entire functions of
  finite order*. Mat. Sb. (N.S.) (1979), 555--581, 647. English translation: Math. USSR-Sb. 37
  (1980), 509--533. [Math-Net.Ru](https://www.mathnet.ru/eng/sm2401)
- [Ha60b] Hayman, W. K., *Slowly growing integral and subharmonic functions*. Comment. Math.
  Helv. 34 (1960), 75--84.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace Erdos1115

/-- A function `γ : ℝ → ℂ` is parametrised by arc length on `[0, ∞)`: for all `0 ≤ a ≤ b` the
variation of `γ` on `[a, b]` is `b - a`. Since the variation dominates the distance between the
endpoints, `γ` is then $1$-Lipschitz on `[0, ∞)`, hence continuous, and has unit speed. Only the
restriction of `γ` to `[0, ∞)` matters. -/
def IsArcLengthParam (γ : ℝ → ℂ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → eVariationOn γ (Set.Icc a b) = ENNReal.ofReal (b - a)

/-- `γ` (arc length parametrised on `[0, ∞)`) is an asymptotic path of `f`:
$f(\gamma(t))\to\infty$ as $t\to\infty$. -/
def IsAsymptoticPath (f : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  IsArcLengthParam γ ∧ Tendsto (fun t : ℝ ↦ ‖f (γ t)‖) atTop atTop

/-- The length $\ell(r)$ of the path `γ` (arc length parametrised on `[0, ∞)`) in the disc
$\lvert z\rvert<r$, that is, the Lebesgue measure of $\{t\ge 0 : \lvert\gamma(t)\rvert<r\}$.
Length is counted with multiplicity. The value is in `ℝ≥0∞`. -/
noncomputable def lengthInDisc (γ : ℝ → ℂ) (r : ℝ) : ℝ≥0∞ :=
  volume {t : ℝ | 0 ≤ t ∧ ‖γ t‖ < r}

/-- The length $\ell(r)$ of a path in the disc $\lvert z\rvert<r$ is monotone in $r$. -/
@[category API, AMS 30]
theorem lengthInDisc_mono (γ : ℝ → ℂ) {r r' : ℝ} (h : r ≤ r') :
    lengthInDisc γ r ≤ lengthInDisc γ r' := by
  unfold lengthInDisc
  exact measure_mono fun t ht ↦ ⟨ht.1, lt_of_lt_of_le ht.2 h⟩

/--
Let $f(z)$ be an entire function of finite order, and let $\Gamma$ be a rectifiable path on which
$f(z)\to \infty$. Let $\ell(r)$ be the length of $\Gamma$ in the disc $\lvert z\rvert<r$.

Find a path for which $\ell(r)$ grows as slowly as possible, and estimate $\ell(r)$ in terms of
$M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$.

In particular, can such a path $\Gamma$ be found for which $\ell(r)\ll r$?

This is Problem 2.41 of [Ha74], where it is attributed to Erdős; see also [HaLi18, Problem 2.41].
The answer is no: Gol'dberg and Eremenko [GoEr79] proved that for every $\rho\in[0,\infty]$ there
is an entire function $f$ of order $\rho$ such that, for any asymptotic curve $\Gamma$ on which
$f\to\infty$, the length of $\Gamma$ in $\lvert z\rvert\leq r$ is not $O(r)$ (see also [HaLi18,
Updates 2.7 and 2.41]). The length in $\lvert z\rvert\leq r$ is at most the length in
$\lvert z\rvert<2r$, so $\ell(r)=O(r)$ for the open disc used here would make the length in the
closed disc $O(r)$ too.

We formalise the last question only: the first part asks for a best possible path and an estimate
in terms of $M(r)$ and has no precise claim to state, so it is not formalised. Reading choices:
$f$ is non-constant (a constant has no path on which $f\to\infty$, which would make the statement
trivially true); finite order is `Erdos516.OfFiniteOrder`; $\Gamma$ is given by its arc length
parametrisation `γ` (every rectifiable path on which $f\to\infty$ has infinite length and can be
reparametrised by arc length, without changing the curve traversed or the length in any disc);
$\ell(r)\ll r$ means $\ell(r)\le Cr$ for some $C$ and all large $r$.

[HaLi18, Problem 2.41] also report that Hayman [Ha60b] (and Piranian) showed that if
$\log M(r)=O((\log r)^2)$, one can take for $\Gamma$ a ray from the origin, so that $\ell(r)=r$.
-/
@[category research solved, question, AMS 30]
theorem erdos_1115 :
    ¬ ∀ f : ℂ → ℂ, Erdos516.OfFiniteOrder f → (¬ ∃ a : ℂ, ∀ z, f z = a) →
      ∃ γ : ℝ → ℂ, IsAsymptoticPath f γ ∧
        ∃ C : ℝ, ∀ᶠ r : ℝ in atTop, lengthInDisc γ r ≤ ENNReal.ofReal (C * r) := by
  sorry

end Erdos1115
