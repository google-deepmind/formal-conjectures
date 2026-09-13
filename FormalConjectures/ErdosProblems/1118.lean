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
# Erdős Problem 1118

*References:*
- [erdosproblems.com/1118](https://www.erdosproblems.com/1118)
- [Ca77] G. Camera, *On the minimum rate of growth of certain classes on integral and
  subharmonic functions, PhD Thesis*. Imperial College, University of London (1977).
- [Go79b] Gol'dberg, A. A., *Sets on which the modulus of an entire function has a lower
  bound*. Sibirsk. Mat. Zh. (1979), 512--518, 691.
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. (1974), 155--180.
-/

open Set Filter MeasureTheory
open scoped ENNReal

namespace Erdos1118

/--
The set $E(c)=\{ z: \lvert f(z)\rvert >c\}$.
-/
def E (f : ℂ → ℂ) (c : ℝ) : Set ℂ := {z | c < ‖f z‖}

/--
The maximum modulus $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$.
-/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/--
The set $T=\{ c>0 : \lvert E(c)\rvert <\infty\}$ of levels at which $E(c)$ has finite plane
measure.
-/
noncomputable def T (f : ℂ → ℂ) : Set ℝ := {c | 0 < c ∧ volume (E f c) < ∞}

/--
Let $f(z)$ be a non-constant entire function such that, for some $c$, the set
$E(c)=\{ z: \lvert f(z)\rvert >c\}$ has finite measure.

What is the minimum growth rate of $f(z)$?

This is Problem 2.40 in [Ha74] where it is attributed to Erdős. Hayman conjectured that
$$
\int_0^\infty \frac{r}{\log\log M(r)}\mathrm{d}r<\infty
$$
is true, and best possible, where $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$.

Hayman's strong conjecture was proved independently by Camera [Ca77] and Gol'dberg [Go79b].
-/
@[category research solved, AMS 30]
theorem erdos_1118.parts.i {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnonconst : ∃ z w, f z ≠ f w) (hE : ∃ c, volume (E f c) < ∞) :
    ∃ R, ∫⁻ r in Ioi R, ENNReal.ofReal (r / Real.log (Real.log (maxModulus f r))) < ∞ := by
  sorry

/--
Hayman conjectured that
$$
\int_0^\infty \frac{r}{\log\log M(r)}\mathrm{d}r<\infty
$$
is true, and best possible, where $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$.

Best possible in the sense of Camera [Ca77]: if $\phi(r)$ increases and
$$
\int_0^\infty \frac{r}{\phi(r)}\mathrm{d}r=\infty,
$$
then there exists an entire $f$ with $\log\log M(r,f)<\phi(r)$ that is bounded outside a set
of finite area.
-/
@[category research solved, AMS 30]
theorem erdos_1118.variants.best_possible {φ : ℝ → ℝ} (hφ : Monotone φ)
    (htop : Tendsto φ atTop atTop)
    (hdiv : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r / φ r) = ∞) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z w, f z ≠ f w) ∧
      (∀ᶠ r in atTop, Real.log (Real.log (maxModulus f r)) < φ r) ∧
      ∃ c, volume (E f c) < ∞ := by
  sorry

/--
Let $f(z)$ be a non-constant entire function such that, for some $c$, the set
$E(c)=\{ z: \lvert f(z)\rvert >c\}$ has finite measure.

If $E(c)$ has finite measure then must there exist $c'<c$ such that $E(c')$ has finite measure?

The second question was answered in the negative by Gol'dberg [Go79b], who proved that if
$T=\{ c>0 : \lvert E(c)\rvert <\infty\}$ then for any $m>0$ there exist entire functions $f$
such that $T=[m,\infty)$ or $T=(m,\infty)$. (It is clear that $T=\emptyset$ and $T=(0,\infty)$
are also possible.)
-/
@[category research solved, AMS 30]
theorem erdos_1118.parts.ii : answer(False) ↔
    ∀ (f : ℂ → ℂ), Differentiable ℂ f → (∃ z w, f z ≠ f w) →
      ∀ c, volume (E f c) < ∞ → ∃ c' < c, volume (E f c') < ∞ := by
  sorry

/--
Gol'dberg [Go79b] proved that if $T=\{ c>0 : \lvert E(c)\rvert <\infty\}$ then for any $m>0$
there exist entire functions $f$ such that $T=[m,\infty)$.
-/
@[category research solved, AMS 30]
theorem erdos_1118.variants.T_Ici {m : ℝ} (hm : 0 < m) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z w, f z ≠ f w) ∧ T f = Ici m := by
  sorry

/--
Gol'dberg [Go79b] proved that if $T=\{ c>0 : \lvert E(c)\rvert <\infty\}$ then for any $m>0$
there exist entire functions $f$ such that $T=(m,\infty)$.
-/
@[category research solved, AMS 30]
theorem erdos_1118.variants.T_Ioi {m : ℝ} (hm : 0 < m) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z w, f z ≠ f w) ∧ T f = Ioi m := by
  sorry

/-- Superlevel sets of a constant function are empty or the whole plane. -/
@[category test, AMS 30]
theorem E_const (a : ℂ) (c : ℝ) :
    E (fun _ => a) c = if c < ‖a‖ then univ else ∅ := by
  ext z
  by_cases h : c < ‖a‖
  · simp [E, h]
  · simp [E, h]

/-- On a nonempty circle the maximum modulus of a constant is the modulus of that constant. -/
@[category test, AMS 30]
theorem maxModulus_const (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    maxModulus (fun _ => a) r = ‖a‖ := by
  have : Nonempty {z : ℂ // ‖z‖ = r} := ⟨⟨(r : ℂ), Complex.norm_of_nonneg hr⟩⟩
  exact ciSup_const

/-- On a nonempty circle the maximum modulus of the identity is the radius. -/
@[category test, AMS 30]
theorem maxModulus_id {r : ℝ} (hr : 0 ≤ r) : maxModulus (id : ℂ → ℂ) r = r := by
  have : Nonempty {z : ℂ // ‖z‖ = r} := ⟨⟨(r : ℂ), Complex.norm_of_nonneg hr⟩⟩
  have h : (fun z : {z : ℂ // ‖z‖ = r} => ‖(z : ℂ)‖) = fun _ => r := by
    ext z
    exact z.property
  simp [maxModulus, h, ciSup_const]

end Erdos1118
