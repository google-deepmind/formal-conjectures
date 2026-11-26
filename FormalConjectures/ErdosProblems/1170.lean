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
# Erdős Problem 1170

*Reference:* [erdosproblems.com/1170](https://www.erdosproblems.com/1170)

*References:*
- [La82] Laver, R. *Saturated ideals and nonregular ultrafilters.* Patras Logic Symposion
  (Patras, 1980), pp. 297–305 (1982).
- [FoHa03] Foreman, M.; Hajnal, A. *A partition relation for successors of large cardinals.*
  Math. Ann. 325 (2003), 583–623.
- [Va99] Vaughan, J.E. *Open problems in topology II*, problem 7.86 (1999).
-/

open Cardinal Ordinal
open scoped Cardinal

namespace Erdos1170

universe u

/-- Local copy of the binary ordinal Ramsey predicate $\alpha \to (\beta, \gamma)^2$:
every 2-coloring of pairs from $\alpha$ admits a red clique of order type $\beta$ or a
blue clique of order type $\gamma$.

Will be replaced by `OrdinalRamsey` from `FormalConjecturesForMathlib/SetTheory/Ordinal/
PartitionRelation.lean` once that lands (see PR #4195). -/
def OrdinalRamsey (α β γ : Ordinal.{u}) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
    (∃ s, blue.IsClique s ∧ typeLT s = γ)

/-- **Diagonal ordinal Ramsey**: $\alpha \to (\beta)^2_2$ — the binary partition with both
sides targeting the same order type $\beta$. -/
abbrev OrdinalDiagonalRamsey (α β : Ordinal.{u}) : Prop :=
  OrdinalRamsey α β β

/- ### The main open problem -/

/--
**Erdős Problem 1170** [Va99, 7.86]. Is it consistent with ZFC that
$\omega_2 \to (\alpha)^2_2$ for every $\alpha < \omega_2$?

Equivalently: is it consistent that $\omega_2$ has the diagonal Ramsey property targeting
every strictly smaller ordinal?

**Status.** OPEN. Two partial results are known (off-diagonal): Laver [La82] showed the
consistency of $\omega_2 \to (\omega_1 \cdot 2 + 1, \alpha)^2$ for all $\alpha < \omega_2$,
and Foreman–Hajnal [FoHa03] showed the consistency of $\omega_2 \to (\omega_1^2 + 1, \alpha)^2$
for all $\alpha < \omega_2$.
-/
@[category research open, AMS 3]
theorem erdos_1170 :
    answer(sorry) ↔ ∀ α : Ordinal.{0}, α < ω_ 2 → OrdinalDiagonalRamsey (ω_ 2) α := by
  sorry

/- ### Known partial results -/

namespace erdos_1170.variants

/--
**Laver (1982).** It is consistent with ZFC that $\omega_2 \to (\omega_1 \cdot 2 + 1, \alpha)^2$
for every $\alpha < \omega_2$ — the off-diagonal Ramsey property of $\omega_2$ with a fixed
red side of $\omega_1 \cdot 2 + 1$ and any blue side below $\omega_2$.
-/
@[category research solved, AMS 3]
theorem laver_1982 :
    answer(sorry) ↔
    ∀ α : Ordinal.{0}, α < ω_ 2 →
      OrdinalRamsey (ω_ 2) ((ω_ 1) * 2 + 1) α := by
  sorry

/--
**Foreman–Hajnal (2003).** It is consistent with ZFC that
$\omega_2 \to (\omega_1^2 + 1, \alpha)^2$ for every $\alpha < \omega_2$, improving Laver
on the red side from $\omega_1 \cdot 2 + 1$ to $\omega_1^2 + 1$.
-/
@[category research solved, AMS 3]
theorem foreman_hajnal_2003 :
    answer(sorry) ↔
    ∀ α : Ordinal.{0}, α < ω_ 2 →
      OrdinalRamsey (ω_ 2) ((ω_ 1) ^ (2 : ℕ) + 1) α := by
  sorry

end erdos_1170.variants

/- ### Sanity checks -/

/-- Foreman–Hajnal strengthens Laver: $\omega_1 \cdot 2 + 1 \le \omega_1^2 + 1$, so any
$(\omega_1^2 + 1, \alpha)^2$ Ramsey arrow gives the $(\omega_1 \cdot 2 + 1, \alpha)^2$
arrow.

Deferred — needs lemmas about ordinal exponentiation $\omega_1^2 = \omega_1 \cdot \omega_1$
and that $2 \le \omega_1$. -/
@[category test, AMS 3]
theorem foreman_hajnal_implies_laver :
    (ω_ 1) * 2 + 1 ≤ (ω_ 1) ^ (2 : ℕ) + 1 := by
  sorry

end Erdos1170
