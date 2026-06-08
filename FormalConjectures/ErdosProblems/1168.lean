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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1168

*Reference:* [erdosproblems.com/1168](https://www.erdosproblems.com/1168)
-/

open Cardinal Ordinal SimpleGraph

namespace Erdos1168

universe u

/--
**Erdős Problem 1168.** Prove that
$$\aleph_{\omega+1} \not\to (\aleph_{\omega+1}, \underbrace{3, 3, \ldots}_{\aleph_0})^2_{\aleph_0}$$
without assuming the generalized continuum hypothesis.

A problem of Erdős, Hajnal, and Rado [EHR65]: the negative arrow is known under GCH;
the open problem asks for a ZFC proof. Here `ω = Ordinal.omega0`, so `ℵ_ (ω + 1)` is
the successor cardinal of the singular `ℵ_ω`.
-/
@[category research open, AMS 5]
theorem erdos_1168 : ¬ CardinalCountableColorRamsey (ℵ_ (ω + 1)) := by
  sorry

namespace erdos_1168.variants

/--
**Erdős–Hajnal–Rado theorem under GCH** [EHR65]: the negative partition relation
$\aleph_{\omega+1} \not\to (\aleph_{\omega+1}, 3, 3, \ldots)^2_{\aleph_0}$ holds
assuming GCH.
-/
@[category research solved, AMS 5]
theorem under_GCH (hGCH : GCH) : ¬ CardinalCountableColorRamsey (ℵ_ (ω + 1)) := by
  sorry

/-- `ℵ_{ω+1}` is strictly greater than `ℵ₀`. -/
@[category test, AMS 5]
example : ℵ₀ < ℵ_ (ω + 1) := by
  rw [← aleph_zero]
  apply aleph_lt_aleph.mpr
  exact omega0_pos.trans_le le_self_add

/-- `ℵ_ω < ℵ_{ω+1}`: the cardinal `ℵ_{ω+1}` is the successor of the singular `ℵ_ω`. -/
@[category test, AMS 5]
example : ℵ_ ω < ℵ_ (ω + 1) := by
  exact aleph_lt_aleph.mpr (lt_add_one ω)

/-- **GCH implies `2^(ℵ_ω) = ℵ_{ω+1}`** — the arithmetic fact used in the
Erdős–Hajnal–Rado [EHR65] proof. Direct from the Jech-style formulation of GCH. -/
@[category test, AMS 5]
theorem GCH_implies_power_aleph_omega (hGCH : GCH) :
    (2 : Cardinal.{0}) ^ ℵ_ ω = ℵ_ (ω + 1) := by
  have h := hGCH ω
  rwa [show Order.succ (ω : Ordinal.{0}) = ω + 1 from (add_one_eq_succ ω)] at h

/-- `ℵ_{ω+1} = Order.succ (ℵ_ω)`: a structural fact used in partition calculus. -/
@[category test, AMS 5]
theorem aleph_omega_succ_is_successor : ℵ_ (ω + 1) = Order.succ (ℵ_ ω) := by
  conv_lhs => rw [show (ω : Ordinal) + 1 = Order.succ ω from (add_one_eq_succ ω).symm]
  exact aleph_succ ω

/--
**Monotonicity**: if `CardinalCountableColorRamsey κ` holds and `μ ≤ κ`, then
`CardinalCountableColorRamsey μ` holds. (Requires ordinal embedding machinery.)
-/
@[category research open, AMS 5]
theorem mono_kappa {μ κ : Cardinal.{u}} (hle : μ ≤ κ)
    (hκ : CardinalCountableColorRamsey κ) : CardinalCountableColorRamsey μ := by
  sorry

end erdos_1168.variants

end Erdos1168
