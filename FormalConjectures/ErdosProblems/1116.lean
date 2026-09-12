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
# Erdős Problem 1116

*References:*
- [erdosproblems.com/1116](https://www.erdosproblems.com/1116)
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. (1974), 155--180.
- [Go78] Gol'dberg, A. A., *Counting functions of sequences of $a$-points for entire functions*.
  Sibirsk. Mat. Ž. (1978), 28--36, 236.
- [To76] Toppila, Sakari, *On the counting function for the $a$-values of a meromorphic function*.
  Ann. Acad. Sci. Fenn. Ser. A I Math. (1976), 565--572.
-/

open Filter

namespace Erdos1116

/--
The Nevanlinna counting function $n(r,a)$: the number of roots of $f(z)=a$ in the disc
$\lvert z\rvert < r$, counted with multiplicity.

Poles of $f$ are not $a$-points for finite $a$. If $f$ is identically $a$, the meromorphic
order is infinite and is recorded as $0$, so this counting function is intended for
non-constant meromorphic $f$.
-/
noncomputable def n (f : ℂ → ℂ) (r : ℝ) (a : ℂ) : ℕ :=
  ∑ᶠ z : ℂ, if ‖z‖ < r then (meromorphicOrderAt (fun w ↦ f w - a) z).untop₀.toNat else 0

/--
For a meromorphic function $f$ let $n(r,a)$ count the number of roots of $f(z)=a$ in the disc
$\lvert z\rvert <r$. Does there exist a meromorphic (or entire) $f$ such that for every $a\neq b$
$$\limsup_{r\to \infty}\frac{n(r,a)}{n(r,b)}=\infty?$$

This is Problem 1.25 in [Ha74], where it is attributed to Erdős.

Gol'dberg [Go78] and Toppila [To76] have constructed entire functions with this property.
-/
@[category research solved, AMS 30]
theorem erdos_1116 : answer(True) ↔
    ∃ f : ℂ → ℂ, Meromorphic f ∧
      ∀ ⦃a b : ℂ⦄, a ≠ b →
        limsup (fun r : ℝ ↦ (n f r a : ENNReal) / n f r b) atTop = ⊤ := by
  sorry

/--
The same question for entire functions. Gol'dberg [Go78] and Toppila [To76] constructed entire
functions with this property.
-/
@[category research solved, AMS 30]
theorem erdos_1116.variants.entire : answer(True) ↔
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ ⦃a b : ℂ⦄, a ≠ b →
        limsup (fun r : ℝ ↦ (n f r a : ENNReal) / n f r b) atTop = ⊤ := by
  sorry

/--
The multiplicity of the unique root of $z \mapsto z - a$ is $1$ at $a$ and $0$ elsewhere.
-/
@[category API, AMS 30]
theorem meromorphicOrderAt_id_sub_eq (a z : ℂ) :
    (meromorphicOrderAt (fun w : ℂ ↦ w - a) z).untop₀.toNat = if z = a then 1 else 0 := by
  by_cases h : z = a
  · subst h
    simp [meromorphicOrderAt_id_sub_const]
  · have hf : AnalyticAt ℂ (fun w : ℂ ↦ w - a) z := by fun_prop
    have hord : meromorphicOrderAt (fun w : ℂ ↦ w - a) z = 0 := by
      rw [hf.meromorphicOrderAt_eq, hf.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 h)]
      simp
    simp [h, hord]

/-- Constants contribute no $a$-points to $n(r,a)$. -/
@[category test, AMS 30]
theorem n_const (c a : ℂ) (r : ℝ) : n (fun _ ↦ c) r a = 0 := by
  unfold n
  refine (finsum_congr fun z ↦ ?_).trans finsum_zero
  split_ifs with _
  · rw [show (fun w : ℂ ↦ (fun _ ↦ c) w - a) = fun _ ↦ c - a from rfl,
      meromorphicOrderAt_const z (c - a)]
    split_ifs <;> simp
  · rfl

/-- For the identity, $n(r,a)$ is $1$ if $\lvert a\rvert < r$ and $0$ otherwise. -/
@[category test, AMS 30]
theorem n_id (r : ℝ) (a : ℂ) : n id r a = if ‖a‖ < r then 1 else 0 := by
  unfold n
  have hfun : (fun w : ℂ ↦ id w - a) = fun w ↦ w - a := rfl
  simp_rw [hfun, meromorphicOrderAt_id_sub_eq]
  rw [finsum_eq_single _ a]
  · simp
  · intro z hz
    simp [hz]

/-- The counting function vanishes for non-positive radii, since $\lvert z\rvert < r$ is empty. -/
@[category test, AMS 30]
theorem n_of_nonpos (f : ℂ → ℂ) {r : ℝ} (a : ℂ) (hr : r ≤ 0) : n f r a = 0 := by
  unfold n
  refine (finsum_congr fun z ↦ ?_).trans finsum_zero
  have : ¬ ‖z‖ < r := not_lt.mpr (hr.trans (norm_nonneg z))
  simp [this]

end Erdos1116
