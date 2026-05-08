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
# Erdős Problem 501

**Verbatim statement (Erdős #501, status O):**
> For every $x\in\mathbb{R}$ let $A_x\subset \mathbb{R}$ be a bounded set with outer measure $<1$. Must there exist an infinite independent set, that is, some infinite $X\subseteq \mathbb{R}$ such that $x\not\in A_y$ for all $x\neq y\in X$?If the sets $A_x$ are closed and have measure $<1$, then must there exist an independent set of size $3$?

**Source:** https://www.erdosproblems.com/501

**Notes:** OPEN


*Reference:* [erdosproblems.com/501](https://www.erdosproblems.com/501)
-/

open Set MeasureTheory
open scoped Cardinal ENNReal

namespace Erdos501

/- ## Setup

For every `x : ℝ` we are given a set `A x ⊆ ℝ`. We say that `X ⊆ ℝ` is an
**independent set** for the family `A` if `x ∉ A y` for all distinct `x y ∈ X`.
This captures the combinatorial independence relation: `x` does not belong to the
set "assigned to" `y`.

The problem concerns outer measure `< 1` on ℝ. For a set `s : Set ℝ` we use
`(MeasureTheory.volume.toOuterMeasure) s`, which equals the Lebesgue outer measure
of `s` (defined for all sets, whether measurable or not). The condition `< 1` is
stated in `ℝ≥0∞` (extended non-negative reals). -/

/-- `X ⊆ ℝ` is an **independent set** for the family `A : ℝ → Set ℝ` if
`x ∉ A y` for all distinct `x y ∈ X`. -/
def IsIndependent (A : ℝ → Set ℝ) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → x ∉ A y

/- ## Main open problem -/

/--
For every `x ∈ ℝ` let `A x ⊆ ℝ` be a bounded set with (Lebesgue) outer measure `< 1`.
Must there exist an infinite independent set, that is, some infinite `X ⊆ ℝ` such
that `x ∉ A y` for all `x ≠ y` in `X`?

This is **open** in full generality (as of 2025).

Known results:
- Erdős and Hajnal [ErHa60] proved the existence of arbitrarily large finite
  independent sets.
- Hechler [He72] showed the answer is **no** assuming the continuum hypothesis (CH).

[ErHa60] Erdős, Paul and Hajnal, András. On some combinatorial problems involving
         complete graphs. Acta Math. Acad. Sci. Hungar. (1960), 395-424.
[He72] Hechler, S. H. A dozen small uncountable cardinals. TOPO 72, Lecture Notes
       in Math. (1972), 207-218. -/
@[category research open, AMS 5]
theorem erdos_501 : answer(sorry) ↔
    ∀ (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) →
      (∀ x, volume.toOuterMeasure (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ IsIndependent A X := by
  sorry

/- ## Variants and partial results -/

/--
**Erdős–Hajnal (1960): arbitrarily large finite independent sets exist.**

For every `n : ℕ` and every family `A : ℝ → Set ℝ` of bounded sets with Lebesgue
outer measure `< 1`, there exists a finite independent set of size at least `n`.

This was proved by Erdős and Hajnal [ErHa60]. -/
@[category research solved, AMS 5]
theorem erdos_501.variants.erdosHajnal_finite : answer(True) ↔
    ∀ (n : ℕ) (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) →
      (∀ x, volume.toOuterMeasure (A x) < 1) →
      ∃ X : Finset ℝ, n ≤ X.card ∧ IsIndependent A (X : Set ℝ) := by
  simp only [true_iff]
  sorry

/--
**Hechler (1972): the answer to the main question is NO, assuming the continuum hypothesis.**

Assuming CH (`ℵ₁ = 𝔠`), there exists a family `A : ℝ → Set ℝ` of bounded sets with
Lebesgue outer measure `< 1` for which no infinite independent set exists.

[He72] Hechler, S. H. A dozen small uncountable cardinals. TOPO 72, Lecture Notes
       in Math. (1972), 207-218. -/
@[category research solved, AMS 5]
theorem erdos_501.variants.hechler_CH : answer(True) ↔
    (ℵ₁ = 𝔠) →
    ∃ (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) ∧
      (∀ x, volume.toOuterMeasure (A x) < 1) ∧
      ¬ ∃ X : Set ℝ, X.Infinite ∧ IsIndependent A X := by
  simp only [true_iff]
  sorry

/--
**Closed sets case: existence of an independent set of size 3.**

If the sets `A x` are closed with Lebesgue measure `< 1`, must there exist an
independent set of size 3?

This is implied by the stronger theorem of Newelski–Pawlikowski–Seredyński below.

[Gl62] Gladysz proved the existence of an independent set of size 2 in this case. -/
@[category research solved, AMS 5]
theorem erdos_501.variants.closed_size3 : answer(True) ↔
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, 3 ≤ X.ncard ∧ IsIndependent A X := by
  simp only [true_iff]
  sorry

/--
**Newelski–Pawlikowski–Seredyński (1987): infinite independent set in the closed case.**

If all the sets `A x` are closed with Lebesgue measure `< 1`, then there **is** an
infinite independent set. This gives a strong affirmative answer to the second
question of Problem 501.

[NPS87] Newelski, L., Pawlikowski, J., and Seredyński, F. Infinite independent sets in
        the closed case. Acta Math. Acad. Sci. Hungar. (1987). -/
@[category research solved, AMS 5]
theorem erdos_501.variants.newelski_pawlikowski_seredynski : answer(True) ↔
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ IsIndependent A X := by
  simp only [true_iff]
  sorry

/--
**Gladysz (1962): independent set of size 2 in the closed case.**

If all the sets `A x` are closed with Lebesgue measure `< 1`, then there exist two
distinct reals `x y` such that `x ∉ A y` and `y ∉ A x`.

This is a weaker result proved by Gladysz [Gl62] before the full Newelski–Pawlikowski–
Seredyński theorem.

[Gl62] Gladysz, S. Some topological properties of independent sets. Colloq. Math. (1962). -/
@[category research solved, AMS 5]
theorem erdos_501.variants.gladysz_size2 : answer(True) ↔
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, 2 ≤ X.ncard ∧ IsIndependent A X := by
  simp only [true_iff]
  sorry

/--
**Trivial lower bound: a single-element set is always independent.**

For any family `A`, any singleton `{x}` is vacuously independent: there are no two
distinct elements. -/
@[category textbook, AMS 5]
theorem erdos_501.variants.singleton_independent (A : ℝ → Set ℝ) (x : ℝ) :
    IsIndependent A {x} := by
  intro a ha b hb hab
  simp only [Set.mem_singleton_iff] at ha hb
  exact absurd (ha ▸ hb ▸ rfl) hab

/--
**Two-element sets: independent iff mutual non-membership.**

A two-element set `{x, y}` (with `x ≠ y`) is independent for `A` if and only if
`x ∉ A y` and `y ∉ A x`. -/
@[category textbook, AMS 5]
theorem erdos_501.variants.pair_independent_iff (A : ℝ → Set ℝ) {x y : ℝ} (hxy : x ≠ y) :
    IsIndependent A {x, y} ↔ x ∉ A y ∧ y ∉ A x := by
  constructor
  · intro h
    exact ⟨h x (Set.mem_insert x {y}) y (Set.mem_insert_of_mem x rfl) hxy,
           h y (Set.mem_insert_of_mem x rfl) x (Set.mem_insert x {y}) hxy.symm⟩
  · intro ⟨hxy', hyx⟩ a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hxy'
    · exact hyx
    · exact absurd rfl hab

/- ## Sanity checks and examples

The following `example` declarations exercise the proved variants and demonstrate that
the hypotheses of the main theorem are non-vacuous. All goals are fully closed: no `sorry`. -/

/-- The constant family `A x = ∅` satisfies all hypotheses of the main problem:
each `A x` is bounded (the empty set is bounded) and has Lebesgue outer measure 0 < 1.
Moreover, all of ℝ is an independent set, showing the conclusion holds trivially.

This demonstrates that the hypotheses are non-vacuous: the family `A x = ∅` is a valid
input to the theorem, and `ℝ` (which is infinite) witnesses the conclusion. -/
@[category test, AMS 5]
example :
    let A : ℝ → Set ℝ := fun _ => ∅
    (∀ x, Bornology.IsBounded (A x)) ∧
    (∀ x, volume.toOuterMeasure (A x) < 1) ∧
    ∃ X : Set ℝ, X.Infinite ∧ IsIndependent A X := by
  refine ⟨fun _ => Bornology.isBounded_empty, fun _ => ?_, Set.univ, Set.infinite_univ, ?_⟩
  · simp
  · intro x _ y _ _ hxAy; exact hxAy

/-- A singleton `{0}` is an independent set for any family `A : ℝ → Set ℝ`,
as witnessed by `erdos_501.variants.singleton_independent`. -/
@[category test, AMS 5]
example (A : ℝ → Set ℝ) : IsIndependent A {0} :=
  erdos_501.variants.singleton_independent A 0

/-- Two reals form an independent set for the empty family `A _ = ∅`:
neither 0 nor 1 belongs to ∅, so both conditions of `pair_independent_iff` hold. -/
@[category test, AMS 5]
example : IsIndependent (fun _ => (∅ : Set ℝ)) {0, 1} := by
  rw [erdos_501.variants.pair_independent_iff _ (by norm_num : (0:ℝ) ≠ 1)]
  exact ⟨Set.notMem_empty _, Set.notMem_empty _⟩

/-- The hypothesis `volume.toOuterMeasure (A x) < 1` is strictly satisfied when
`A x = {x}` (a singleton), since Lebesgue measure of a singleton is 0. -/
@[category test, AMS 5]
example (x : ℝ) : volume.toOuterMeasure ({x} : Set ℝ) < 1 := by
  simp [Measure.toOuterMeasure_apply]

/-- The boundary case: the measure condition `< 1` is sharp. An interval of length ≥ 1
has Lebesgue measure ≥ 1, so it would fail the hypothesis. Here `[0, 1]` has measure exactly 1. -/
@[category test, AMS 5]
example : volume.toOuterMeasure (Set.Icc (0:ℝ) 1) = 1 := by
  simp [Measure.toOuterMeasure_apply, Real.volume_Icc]

end Erdos501
