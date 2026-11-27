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
# Erdős Problem 1218

*References:*
- [erdosproblems.com/1218](https://www.erdosproblems.com/1218)
- [EHR65] Erdős, P., Hajnal, A. and Rado, R., *Partition relations for cardinal numbers*.
  Acta Math. Acad. Sci. Hungar. (1965), 93-196.
- [ErHa71] Erdős, P. and Hajnal, A., *Unsolved problems in set theory*. Axiomatic Set Theory,
  Proc. Sympos. Pure Math. XIII Part I (1971), 17-48.
- [Ko25b] Komjáth, Péter, *The Erdős–Hajnal problem list*. Bull. Symb. Log. (2025), 418-461.
-/

@[expose] public section

open Cardinal Ordinal Combinatorics

namespace Erdos1218

/-- Targets for a partition relation with $\aleph_0$ colours: colour $0$ has target $\kappa_0$,
and every other colour has target $\kappa$. This is the notation $(\kappa_0,\kappa,\kappa,\ldots)$
with countably many copies of $\kappa$. -/
noncomputable def targets (κ₀ κ : Cardinal.{0}) : (ω : Ordinal.{0}).ToType → Cardinal.{0} :=
  fun i ↦ if typein (α := (ω : Ordinal.{0}).ToType) (· < ·) i = 0 then κ₀ else κ

/-- Raising the first target raises every target. -/
@[category API, AMS 3 5]
theorem targets_mono {κ₀ κ₀' : Cardinal.{0}} (κ : Cardinal.{0}) (h : κ₀ ≤ κ₀') (i) :
    targets κ₀ κ i ≤ targets κ₀' κ i := by
  unfold targets
  split_ifs <;> simp [h]

/-- Colour $0$ has target $\kappa_0$. -/
@[category test, AMS 3 5]
theorem targets_zero (κ₀ κ : Cardinal.{0}) :
    targets κ₀ κ (enum (α := (ω : Ordinal.{0}).ToType) (· < ·) ⟨0, by simp [omega0_pos]⟩) =
      κ₀ := by
  simp only [targets]
  erw [typein_enum]
  exact if_pos rfl

/-- Colour $1$ has target $\kappa$. -/
@[category test, AMS 3 5]
theorem targets_one (κ₀ κ : Cardinal.{0}) :
    targets κ₀ κ (enum (α := (ω : Ordinal.{0}).ToType) (· < ·) ⟨1, by simp [one_lt_omega0]⟩) =
      κ := by
  simp only [targets]
  erw [typein_enum]
  exact if_neg one_ne_zero

/-- There are $\aleph_0$ colours. -/
@[category test, AMS 3 5]
theorem mk_colours : #(ω : Ordinal.{0}).ToType = ℵ₀ := by
  simp

/-- With $\beta=\omega_{\omega+1}$, the cardinal $\aleph_\beta$ has cofinality
$\aleph_{\omega+1}$. -/
@[category test, AMS 3 5]
theorem cof_omega_omega_add_one : (ω_ (ω_ (ω + 1))).cof = ℵ_ (ω + 1) := by
  rw [cof_omega (isSuccLimit_omega _), cof_omega_add_one]

/-- With $\beta=\omega_{\omega+1}$, the cardinal $\aleph_\beta$ is singular, since its cofinality
$\aleph_{\omega+1}$ is smaller. -/
@[category test, AMS 3 5]
theorem aleph_omega_add_one_lt : ℵ_ (ω + 1) < ℵ_ (ω_ (ω + 1)) := by
  rw [aleph_lt_aleph, lt_omega_iff_card_lt]
  simp

/--
Assume the Generalised Continuum Hypothesis and let $\beta=\omega_{\omega+1}$. Is it true that
$$\aleph_{\beta+1} \not\to (\aleph_\beta,4,\ldots,4)^3$$
(where there are countably infinite many copies of $4$)?

A problem of Erdős, Hajnal, and Rado. In [ErHa71] Erdős and Hajnal describe this as the only
problem of this type (concerning generalisations of Ramsey's theorem for cardinal numbers), not
involving strongly inaccessible cardinals, that remains unsolved assuming GCH.
-/
@[category research open, question, AMS 3 5]
theorem erdos_1218 :
    GCH → ¬ cardinalPartitionRel (ℵ_ (ω_ (ω + 1) + 1)) 3 ω (targets (ℵ_ (ω_ (ω + 1))) 4) := by
  sorry

/--
Komjáth [Ko25b, Problem 1] states the problem with first target
$\lambda=\aleph_{\beta+1}$ instead of $\aleph_\beta$: assuming GCH,
$$\aleph_{\beta+1} \not\to (\aleph_{\beta+1},4,4,\ldots)^3.$$
This follows from `erdos_1218`, see `erdos_1218.variants.komjath_of_erdos_1218`.
-/
@[category research open, question, AMS 3 5]
theorem erdos_1218.variants.komjath :
    GCH → ¬ cardinalPartitionRel (ℵ_ (ω_ (ω + 1) + 1)) 3 ω (targets (ℵ_ (ω_ (ω + 1) + 1)) 4) := by
  sorry

/-- The statement of `erdos_1218` implies that of `erdos_1218.variants.komjath`, since a negative
partition relation stays negative when a target grows. -/
@[category test, AMS 3 5]
theorem erdos_1218.variants.komjath_of_erdos_1218
    (h : GCH → ¬ cardinalPartitionRel (ℵ_ (ω_ (ω + 1) + 1)) 3 ω (targets (ℵ_ (ω_ (ω + 1))) 4)) :
    GCH → ¬ cardinalPartitionRel (ℵ_ (ω_ (ω + 1) + 1)) 3 ω
      (targets (ℵ_ (ω_ (ω + 1) + 1)) 4) :=
  fun hG hrel ↦ h hG (hrel.mono (targets_mono 4 (aleph_le_aleph.2 (Order.le_succ _))))

end Erdos1218
