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
# Erdős Problem 1172

*Reference:* [erdosproblems.com/1172](https://www.erdosproblems.com/1172)
-/

open Cardinal Ordinal

namespace Erdos1172

/--
**Erdős–Hajnal Problem 1172, Part 1.** Under GCH,
$\omega_3 \to (\omega_2, \omega_1 + 2)^2$.
-/
@[category research open, AMS 5]
theorem erdos_1172.part1 (hGCH : GCH) :
    OrdinalRamsey (ω_ 3) (ω_ 2) (ω_ 1 + 2) := by
  sorry

/--
**Erdős–Hajnal Problem 1172, Part 2.** Under GCH,
$\omega_3 \to (\omega_2 + \omega_1, \omega_2 + \omega)^2$.
-/
@[category research open, AMS 5]
theorem erdos_1172.part2 (hGCH : GCH) :
    OrdinalRamsey (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω) := by
  sorry

/--
**Erdős–Hajnal Problem 1172, Part 3.** Under GCH,
$\omega_2 \to (\omega_1^{\omega+2} + 2, \omega_1 + 2)^2$.
-/
@[category research open, AMS 5]
theorem erdos_1172.part3 (hGCH : GCH) :
    OrdinalRamsey (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2) := by
  sorry

/--
**Erdős–Hajnal Problem 1172, Part 4.** Is
$\omega_2 \to (\omega_1 + \omega)^2_2$ consistent with GCH?

Lean operates inside a fixed model of its set theory, so "consistent with ZFC + GCH"
cannot be stated directly; we record this as an `answer(sorry)` consistency placeholder.
-/
@[category research open, AMS 5]
theorem erdos_1172.part4 : answer(sorry) ↔
    (GCH ∧ OrdinalRamsey (ω_ 2) (ω_ 1 + ω) (ω_ 1 + ω)) := by
  sorry

/--
**Erdős–Hajnal Problem 1172** (combined): all three GCH-only partition relations
(parts 1–3) hold. Part 4 is a separate consistency question, captured by
`erdos_1172.part4`.
-/
@[category research open, AMS 5]
theorem erdos_1172 (hGCH : GCH) :
    OrdinalRamsey (ω_ 3) (ω_ 2) (ω_ 1 + 2) ∧
    OrdinalRamsey (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω) ∧
    OrdinalRamsey (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2) := by
  sorry

/--
**Erdős–Rado theorem** [ER56] specialized under GCH:
$\omega_2 \to (\omega_1 + 1, \omega_1 + 1)^2$. Under GCH, $(2^{\aleph_0})^+ = \aleph_2$,
so the Erdős–Rado theorem at $\kappa = \aleph_0$ gives a monochromatic clique of order
type $\omega_1 + 1$ in any 2-coloring of $K_{\omega_2}$. The statements in Problem 1172
seek strictly larger homogeneous sets and represent open extensions of this theorem.
-/
@[category research solved, AMS 5]
theorem erdos_rado_binary_instance (hGCH : GCH) :
    OrdinalRamsey (ω_ 2) (ω_ 1 + 1) (ω_ 1 + 1) := by
  sorry

/-- `ω_ 1 < ω_ 2 < ω_ 3`. -/
@[category test, AMS 5]
example : ω_ 1 < ω_ 2 ∧ ω_ 2 < ω_ 3 := by
  exact ⟨Ordinal.omega_lt_omega.mpr one_lt_two,
         Ordinal.omega_lt_omega.mpr (by norm_num)⟩

/-- GCH implies CH. -/
@[category test, AMS 5]
example (h : GCH) : CH := h.toCH

/-- `ω_ 1 + 2 < ω_ 2` (since `ω_ 2` is principal under addition). -/
@[category test, AMS 5]
example : ω_ 1 + 2 < ω_ 2 := by
  apply principal_add_omega
  · exact Ordinal.omega_lt_omega.mpr one_lt_two
  · calc (2 : Ordinal) < ω := by exact_mod_cast Ordinal.nat_lt_omega0 2
      _ ≤ ω_ 2 := omega0_le_omega 2

/-- The ordinal `ω_ 1 ^ (ω + 2)` from Part 3 is positive. -/
@[category test, AMS 5]
example : 0 < ω_ 1 ^ (ω + 2) := Ordinal.opow_pos _ (Ordinal.omega_pos 1)

end Erdos1172
