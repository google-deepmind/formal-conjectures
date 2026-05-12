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
# Erdős Problem 596

*References:*
- [erdosproblems.com/596](https://www.erdosproblems.com/596)
- [Er87] Erdős, Paul, Problems and results on set systems and hypergraphs. Extremal problems
  for finite sets (Visegrád, 1991), Bolyai Soc. Math. Stud. (1994), 217-227.
- [NeRo75] Nešetřil, Jaroslav and Rödl, Vojtěch, Type theory of partition problems of graphs.
  Recent advances in graph theory (Proc. Second Czechoslovak Sympos., Prague, 1974),
  Academia, Prague (1975), 405-412.
-/

open SimpleGraph Set

namespace Erdos596

/-- An **`n`-edge-colouring** of `H` on `V` is a family `c : Fin n → SimpleGraph V` of
pairwise disjoint subgraphs whose union equals `H`. The disjointness condition guarantees
that each edge of `H` is assigned to exactly one colour class. -/
def IsNEdgeColouring {V : Type*} (H : SimpleGraph V) (n : ℕ) (c : Fin n → SimpleGraph V) :
    Prop :=
  H = ⨆ i, c i ∧ ∀ i j, i ≠ j → Disjoint (c i) (c j)

/-- A **countable edge-colouring** of `H` on `V` is a family `c : ℕ → SimpleGraph V` of
pairwise disjoint subgraphs whose union equals `H`. -/
def IsCountableEdgeColouring {V : Type*} (H : SimpleGraph V) (c : ℕ → SimpleGraph V) : Prop :=
  H = ⨆ i, c i ∧ ∀ i j, i ≠ j → Disjoint (c i) (c j)

/-- The **finite Ramsey property** for the pair $(G_1, G_2)$: for every $n \geq 1$, there
exists a $G_1$-free graph `H` on some vertex type in `Type` (universe 0) such that every
`n`-edge-colouring of `H` contains a monochromatic copy of $G_2$. -/
def HasFiniteRamseyProperty {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∃ (V : Type) (H : SimpleGraph V),
    G₁.Free H ∧
    ∀ (c : Fin n → SimpleGraph V), IsNEdgeColouring H n c →
      ∃ i, G₂ ⊑ c i

/-- The **countable Ramsey escape property** for the pair $(G_1, G_2)$: every $G_1$-free
graph `H` on a `Type`-valued vertex type has a countable edge-colouring in which every
colour class is $G_2$-free. -/
def HasCountableRamseyEscape {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  ∀ (W : Type) (H : SimpleGraph W),
    G₁.Free H →
    ∃ (d : ℕ → SimpleGraph W),
      IsCountableEdgeColouring H d ∧ ∀ j, G₂.Free (d j)

/-- A pair $(G_1, G_2)$ is **Erdős–Hajnal exceptional** if it has both the finite Ramsey
property and the countable Ramsey escape property. -/
def IsErdosHajnalExceptional {U₁ U₂ : Type*}
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) : Prop :=
  HasFiniteRamseyProperty G₁ G₂ ∧ HasCountableRamseyEscape G₁ G₂

/--
**Erdős Problem 596**: For which graphs $G_1, G_2$ is it true that
(1) for every $n \geq 1$ there is a graph $H$ without a $G_1$ but if the edges of $H$ are
    $n$-coloured then there is a monochromatic copy of $G_2$, and yet
(2) for every graph $H$ without a $G_1$ there is an $\aleph_0$-colouring of the edges of $H$
    without a monochromatic $G_2$?

A problem of Erdős and Hajnal [Er87].

Erdős and Hajnal originally conjectured that no such pair $(G_1, G_2)$ exists, but
$(C_4, C_6)$ is an example: Nešetřil and Rödl [NeRo75] established the first property and
Erdős and Hajnal established the second. The problem is to characterize **all** such pairs.

See Problem [595] for the specific question of whether $(K_4, K_3)$ is such a pair.

**Formalization:** The Erdős/Hajnal question is to *characterize* the class of exceptional
pairs, not merely to prove the class is nonempty (which is already settled by `(C_4, C_6)`).
We therefore put the conjectural characterizing predicate behind `answer(sorry)` and assert
that it agrees with `IsErdosHajnalExceptional` for every pair `(G₁, G₂)`. The mere
existence of one exceptional pair is recorded separately as
`erdos_596.variants.exists_exceptional`.

**Status:** OPEN.
-/
@[category research open, AMS 5]
theorem erdos_596 :
    ∀ {U₁ U₂ : Type} (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂),
      IsErdosHajnalExceptional G₁ G₂ ↔
      (answer(sorry) : ∀ {U₁ U₂ : Type}, SimpleGraph U₁ → SimpleGraph U₂ → Prop) G₁ G₂ := by
  sorry

/--
**Existence of an Erdős–Hajnal exceptional pair**: there is at least one pair $(G_1, G_2)$
that is exceptional. This was the original Erdős–Hajnal conjecture's negation; it is
witnessed by $(C_4, C_6)$ via [NeRo75] and [Er87]. The full open question (`erdos_596`)
asks to characterize *all* such pairs.

**Status:** SOLVED.
-/
@[category research solved, AMS 5]
theorem erdos_596.variants.exists_exceptional :
    ∃ (U₁ U₂ : Type) (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂),
      IsErdosHajnalExceptional G₁ G₂ := by
  sorry

/--
**The countable Ramsey escape holds for $(C_4, C_6)$**: Every $C_4$-free graph is a countable
union of trees (Erdős and Hajnal [Er87]). Trees are acyclic, hence $C_6$-free, giving the
countable Ramsey escape for $(C_4, C_6)$.

**Status:** SOLVED (Erdős–Hajnal [Er87]).
-/
@[category research solved, AMS 5]
theorem erdos_596.variants.C4_free_countable_escape :
    HasCountableRamseyEscape (cycleGraph 4) (cycleGraph 6) := by
  -- Every C₄-free graph is a countable union of trees (Erdős–Hajnal).
  -- Trees contain no cycles, hence are C₆-free.
  sorry

/--
**The finite Ramsey property holds for $(C_4, C_6)$**: For every $n \geq 1$, there exists a
$C_4$-free graph whose edges cannot be $n$-coloured without a monochromatic $C_6$.

**Status:** SOLVED (Nešetřil–Rödl [NeRo75]).
-/
@[category research solved, AMS 5]
theorem erdos_596.variants.C4_C6_finite_ramsey :
    HasFiniteRamseyProperty (cycleGraph 4) (cycleGraph 6) := by
  -- Nešetřil and Rödl [NeRo75] established this.
  sorry

/--
**The pair $(C_4, C_6)$ is Erdős–Hajnal exceptional**: It disproves the original Erdős–Hajnal
conjecture. Nešetřil–Rödl [NeRo75] established the finite Ramsey property and Erdős–Hajnal
[Er87] established the countable escape (every $C_4$-free graph is a countable union of trees).

**Status:** SOLVED.
-/
@[category research solved, AMS 5]
theorem erdos_596.variants.C4_C6_is_exceptional :
    IsErdosHajnalExceptional (cycleGraph 4) (cycleGraph 6) :=
  ⟨erdos_596.variants.C4_C6_finite_ramsey, erdos_596.variants.C4_free_countable_escape⟩

/--
**The original Erdős–Hajnal conjecture is false**: Erdős and Hajnal conjectured that no pair
$(G_1, G_2)$ is Erdős–Hajnal exceptional. This is refuted by the pair $(C_4, C_6)$.

**Status:** SOLVED (FALSE).
-/
@[category research solved, AMS 5]
theorem erdos_596.variants.original_conjecture_is_false : answer(False) ↔
    ∀ {U₁ U₂ : Type} (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂),
      ¬IsErdosHajnalExceptional G₁ G₂ := by
  -- The pair (C₄, C₆) witnesses the falsity of the conjecture (Nešetřil–Rödl + Erdős–Hajnal).
  sorry

/--
**Connection to Problem 595**: Whether $(K_4, K_3)$ is Erdős–Hajnal exceptional is precisely
the content of Erdős Problem 595. The finite Ramsey property holds (Folkman [1970],
Nešetřil–Rödl [NeRo75]). The open part is whether every $K_4$-free graph is a countable
union of triangle-free graphs, which is exactly the countable Ramsey escape for $(K_4, K_3)$.

**Status:** OPEN (= Problem 595).
-/
@[category research open, AMS 5]
theorem erdos_596.variants.K4_K3_exceptional_iff : answer(sorry) ↔
    IsErdosHajnalExceptional (completeGraph (Fin 4)) (completeGraph (Fin 3)) := by
  sorry

/--
**The finite Ramsey property holds for $(K_4, K_3)$** (Folkman [1970], Nešetřil–Rödl
[NeRo75]): for every $n \geq 1$, there exists a $K_4$-free graph whose edges cannot be
$n$-coloured without a monochromatic triangle.

**Status:** SOLVED.
-/
@[category research solved, AMS 5]
theorem erdos_596.variants.K4_K3_finite_ramsey :
    HasFiniteRamseyProperty (completeGraph (Fin 4)) (completeGraph (Fin 3)) := by
  -- Folkman (1970) and Nešetřil–Rödl (1975) independently proved this.
  sorry

end Erdos596
