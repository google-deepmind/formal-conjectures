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
# Erdős Problem 596

*References:*
- [erdosproblems.com/596](https://www.erdosproblems.com/596)
- [Er87] Erdős, P., *Some problems on finite and infinite graphs*, in *Logic and combinatorics*
  (Arcata, Calif., 1985), Contemp. Math. **65** (1987), 223–228.
- [NeRo75] Nešetřil, J. and Rödl, V., *Type theory of partition properties of graphs*, in
  *Infinite and finite sets* (Colloq., Keszthely, 1973), Colloq. Math. Soc. János Bolyai **10**
  (1975), 405–412.
- [NeRo87] Nešetřil, J. and Rödl, V., *Strong Ramsey theorems for Steiner systems*,
  *Trans. Amer. Math. Soc.* **303** (1987), 183–192.
-/

@[expose] public section

open SimpleGraph

namespace Erdos596

def erdos_596.answer {U₁ : Type} {U₂ : Type} : SimpleGraph U₁ → SimpleGraph U₂ → Prop := sorry

/--
**Erdős Problem 596** (Erdős–Hajnal, [Er87]). For which finite graph pairs $(G_1, G_2)$ is it
true that

  (1) for every $n \geq 1$ there is a graph $H$ without a $G_1$ such that any
      $n$-colouring of $H$'s edges contains a monochromatic $G_2$, and yet
  (2) for every graph $H$ without a $G_1$ there is an $\aleph_0$-colouring of $H$'s edges
      with no monochromatic $G_2$?

Erdős and Hajnal originally conjectured that no such pair exists; but $(C_4, C_6)$
witnesses it (Nešetřil–Rödl + Erdős–Hajnal). The full question is to characterise the
class of all such pairs, recorded here as the unknown `erdos_596.answer`.

See Problem 595 for the specific case $(G_1, G_2) = (K_4, K_3)$.
-/
@[category research open, question value, AMS 5]
theorem erdos_596 :
    ∀ {U₁ U₂ : Type} [Finite U₁] [Finite U₂] (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂),
      IsErdosHajnalExceptional G₁ G₂ ↔ erdos_596.answer G₁ G₂ := by
  sorry

/-- Finite Erdős–Hajnal exceptional pairs exist — recorded as a known direction of `erdos_596`. -/
@[category research solved, AMS 5]
theorem erdos_596.variants.exists_exceptional :
    ∃ (U₁ U₂ : Type) (_ : Finite U₁) (_ : Finite U₂)
      (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂),
      IsErdosHajnalExceptional G₁ G₂ := by
  sorry

/-- Every $C_4$-free graph is a countable union of trees (Erdős–Hajnal [Er87]); trees are
acyclic, hence $C_6$-free, giving the countable Ramsey escape for $(C_4, C_6)$. -/
@[category research solved, AMS 5]
theorem erdos_596.variants.C4_free_countable_escape :
    HasCountableRamseyEscape (cycleGraph 4) (cycleGraph 6) := by
  sorry

/-- Nešetřil–Rödl [NeRo87]: for every $n \geq 1$ there is a $C_4$-free graph whose edges
cannot be $n$-coloured without a monochromatic $C_6$. -/
@[category research solved, AMS 5]
theorem erdos_596.variants.C4_C6_finite_ramsey :
    HasFiniteRamseyProperty (cycleGraph 4) (cycleGraph 6) := by
  sorry

/-- The pair $(C_4, C_6)$ is Erdős–Hajnal exceptional; combines `C4_C6_finite_ramsey` and
`C4_free_countable_escape`. -/
@[category research solved, AMS 5]
theorem erdos_596.variants.C4_C6_is_exceptional :
    IsErdosHajnalExceptional (cycleGraph 4) (cycleGraph 6) :=
  ⟨erdos_596.variants.C4_C6_finite_ramsey, erdos_596.variants.C4_free_countable_escape⟩

/-- The original Erdős–Hajnal conjecture (that no finite exceptional pair exists) is **false** —
witnessed by $(C_4, C_6)$ via `C4_C6_is_exceptional`. -/
@[category research solved, question, AMS 5]
theorem erdos_596.variants.original_conjecture_is_false :
    ¬ ∀ {U₁ U₂ : Type} [Finite U₁] [Finite U₂] (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂),
      ¬IsErdosHajnalExceptional G₁ G₂ := by
  sorry

/-- Whether $(K_4, K_3)$ is Erdős–Hajnal exceptional is precisely the content of
Erdős Problem 595. The finite Ramsey property holds (Folkman 1970, Nešetřil–Rödl
[NeRo75]); the open part is whether every $K_4$-free graph is a countable union of
triangle-free graphs. -/
@[category research open, question, AMS 5]
theorem erdos_596.variants.K4_K3_exceptional_iff :
    IsErdosHajnalExceptional (completeGraph (Fin 4)) (completeGraph (Fin 3)) := by
  sorry

/-- Folkman 1970 / Nešetřil–Rödl [NeRo75]: for every $n \geq 1$ there is a $K_4$-free
graph whose edges cannot be $n$-coloured without a monochromatic triangle. -/
@[category research solved, AMS 5]
theorem erdos_596.variants.K4_K3_finite_ramsey :
    HasFiniteRamseyProperty (completeGraph (Fin 4)) (completeGraph (Fin 3)) := by
  sorry

/- ## Sanity checks -/

/-- The empty graph on `Fin 0` is `Free` of any nontrivial subgraph (vacuous). This is the
simplest non-trivial witness to `G₁.Free H` appearing in `HasFiniteRamseyProperty`. -/
@[category test, AMS 5]
theorem erdos_596.test.empty_is_free :
    (cycleGraph 4).Free (⊥ : SimpleGraph (Fin 0)) :=
  fun ⟨f⟩ => Fin.elim0 (f.toEmbedding 0)

end Erdos596
