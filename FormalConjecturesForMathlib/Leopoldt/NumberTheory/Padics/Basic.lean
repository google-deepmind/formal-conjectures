/-
Copyright 2025 The Formal Conjectures Authors.

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
public import Mathlib

/-!
# `p`-adic integers: vanishing and approximation

Three small facts about `ℤ_[p]` used by the Leopoldt development: an element in every power of
the maximal ideal is zero; the integer approximants `PadicInt.appr` converge to their element,
measured in `ℂ_[p]`; and the approximation `a = a.appr n + pⁿ c` is exact.

Staging area: kept in the `Leopoldt` namespace. Narrow the imports and pick final namespaces
before upstreaming.
-/

@[expose] public section

open Filter

/-- `a = a.appr n + pⁿ c` for some `c ∈ ℤ_p`: the `n`-th integer approximation of `a` is exact
modulo `pⁿ` (`PadicInt.appr_spec`). -/
theorem PadicInt.exists_eq_appr_add_pow_mul {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) (n : ℕ) :
    ∃ c : ℤ_[p], a = a.appr n + (p : ℤ_[p]) ^ n * c := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)
  exact ⟨c, by linear_combination hc⟩

namespace Leopoldt

section Implicit

variable {p : ℕ} [Fact p.Prime]

lemma eq_zero_of_forall_mem_span_pow {x : ℤ_[p]}
    (h : ∀ n : ℕ, x ∈ Ideal.span {(p : ℤ_[p]) ^ n}) : x = 0 := by
  by_contra hx
  have := (PadicInt.norm_le_pow_iff_mem_span_pow x (x.valuation + 1)).2 (h _)
  rw [PadicInt.norm_eq_zpow_neg_valuation hx,
    zpow_le_zpow_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)] at this
  omega

end Implicit

section Explicit

variable (p : ℕ) [Fact p.Prime]

/--
The `p`-adic distance from the integer approximant `a.appr m` to `a`, measured in
$\mathbb{C}_p$, is at most $p^{-m}$ (`PadicInt.appr_spec`).
-/
theorem norm_appr_sub_le (a : ℤ_[p]) (m : ℕ) :
    ‖((a.appr m : ℕ) : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ m := by
  have hcast : ((a.appr m : ℕ) : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])
      = algebraMap ℚ_[p] ℂ_[p] (((a.appr m : ℤ_[p]) - a : ℤ_[p]) : ℚ_[p]) := by
    push_cast
    ring
  rw [hcast, show algebraMap ℚ_[p] ℂ_[p] (((a.appr m : ℤ_[p]) - a : ℤ_[p]) : ℚ_[p])
    = ((((a.appr m : ℤ_[p]) - a : ℤ_[p]) : ℚ_[p]) : ℂ_[p]) from rfl,
    PadicComplex.norm_extends', ← PadicInt.norm_def, norm_sub_rev]
  calc ‖(a - (a.appr m : ℤ_[p]))‖ ≤ (p : ℝ) ^ (-m : ℤ) :=
        (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 (PadicInt.appr_spec m a)
    _ = ((p : ℝ)⁻¹) ^ m := by rw [zpow_neg, zpow_natCast, inv_pow]

/--
The `p`-adic integer `a` is the limit in $\mathbb{C}_p$ of its integer approximants
`a.appr m`.
-/
theorem tendsto_appr_cast (a : ℤ_[p]) :
    Tendsto (fun n ↦ ((a.appr n : ℕ) : ℂ_[p])) atTop
      (nhds (algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p]))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (norm_appr_sub_le p a) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by rw [inv_lt_one₀] <;> linarith)

end Explicit

end Leopoldt
