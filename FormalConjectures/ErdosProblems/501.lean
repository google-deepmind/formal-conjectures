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

*References:*
- [erdosproblems.com/501](https://www.erdosproblems.com/501)
- [Er61] Erdős, Paul, Some unsolved problems. Magyar Tud. Akad. Mat. Kutató Int. Közl. 6
  (1961), 221-254.
- [ErHa71] Erdős, Paul and Hajnal, András, Unsolved problems in set theory. Axiomatic Set
  Theory, Proc. Sympos. Pure Math. XIII Part I (1971), 17-48.
- [ErHa60] Erdős, Paul and Hajnal, András. On some combinatorial problems involving
  complete graphs. Acta Math. Acad. Sci. Hungar. (1960), 395-424.
- [Gl62] Gladysz, S. Some topological properties of independent sets. Colloq. Math. (1962).
- [He72] Hechler, S. H. A dozen small uncountable cardinals. TOPO 72, Lecture Notes
  in Math. (1972), 207-218.
- [NPS87] Newelski, L., Pawlikowski, J., and Seredyński, F. Infinite independent sets in
  the closed case. Acta Math. Acad. Sci. Hungar. (1987).
-/

open Set MeasureTheory
open scoped Cardinal ENNReal

namespace Erdos501

/- ## Setup

For every `x : ℝ` we are given a set `A x ⊆ ℝ`. We say that `X ⊆ ℝ` is an
**independent set** for the family `A` if `x ∉ A y` for all distinct `x y ∈ X`.
This is exactly `X.Pairwise (fun x y => x ∉ A y)`; we inline this rather than
introducing a custom predicate so that all `Set.Pairwise` lemmas apply.

The problem concerns outer measure `< 1` on ℝ. For a set `s : Set ℝ` we use
`(MeasureTheory.volume.toOuterMeasure) s`, which equals the Lebesgue outer measure
of `s` (defined for all sets, whether measurable or not). The condition `< 1` is
stated in `ℝ≥0∞` (extended non-negative reals). -/

/- ## Main open problem -/

/--
For every $x \in \mathbb{R}$ let $A_x \subset \mathbb{R}$ be a bounded set with outer measure
$< 1$. Must there exist an infinite independent set, that is, some infinite $X \subseteq
\mathbb{R}$ such that $x \notin A_y$ for all $x \neq y \in X$?

If the sets $A_x$ are closed and have measure $< 1$, then must there exist an independent set
of size $3$?

Known results: Erdős–Hajnal [ErHa60] proved the existence of arbitrarily large finite
independent sets. Hechler [He72] showed the answer is **no** assuming the continuum
hypothesis. -/
@[category research open, AMS 5 28]
theorem erdos_501 : answer(sorry) ↔
    ∀ (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) →
      (∀ x, volume.toOuterMeasure (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  sorry

/- ## Variants and partial results -/

/--
**Erdős–Hajnal (1960): arbitrarily large finite independent sets exist.**

For every `n : ℕ` and every family `A : ℝ → Set ℝ` of bounded sets with Lebesgue
outer measure `< 1`, there exists a finite independent set of size at least `n`.

This was proved by Erdős and Hajnal [ErHa60]. -/
@[category research solved, AMS 5 28]
theorem erdos_501.variants.erdosHajnal_finite : answer(True) ↔
    ∀ (n : ℕ) (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) →
      (∀ x, volume.toOuterMeasure (A x) < 1) →
      ∃ X : Finset ℝ, n ≤ X.card ∧ (X : Set ℝ).Pairwise (fun x y => x ∉ A y) := by
  simp only [true_iff]
  sorry

/--
**Hechler (1972) [He72]: the answer to the main question is NO, assuming the continuum
hypothesis.**

Assuming CH (`ℵ₁ = 𝔠`), there exists a family `A : ℝ → Set ℝ` of bounded sets with
Lebesgue outer measure `< 1` for which no infinite independent set exists. -/
@[category research solved, AMS 5 28]
theorem erdos_501.variants.hechler_CH : answer(True) ↔
    (ℵ₁ = 𝔠) →
    ∃ (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) ∧
      (∀ x, volume.toOuterMeasure (A x) < 1) ∧
      ¬ ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  simp only [true_iff]
  sorry

/--
**Closed sets case: existence of an independent set of size 3.**

If the sets `A x` are closed with Lebesgue measure `< 1`, must there exist an
independent set of size 3?

This is implied by the stronger theorem of Newelski–Pawlikowski–Seredyński [NPS87] below;
Gladysz [Gl62] earlier proved the existence of an independent set of size 2. -/
@[category research solved, AMS 5 28]
theorem erdos_501.variants.closed_size3 : answer(True) ↔
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, 3 ≤ X.ncard ∧ X.Pairwise (fun x y => x ∉ A y) := by
  simp only [true_iff]
  sorry

/--
**Newelski–Pawlikowski–Seredyński (1987) [NPS87]: infinite independent set in the closed case.**

If all the sets `A x` are closed with Lebesgue measure `< 1`, then there **is** an
infinite independent set. This gives a strong affirmative answer to the second
question of Problem 501. -/
@[category research solved, AMS 5 28]
theorem erdos_501.variants.newelski_pawlikowski_seredynski : answer(True) ↔
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  simp only [true_iff]
  sorry

/--
**Gladysz (1962) [Gl62]: independent set of size 2 in the closed case.**

If all the sets `A x` are closed with Lebesgue measure `< 1`, then there exist two
distinct reals `x y` such that `x ∉ A y` and `y ∉ A x`.

This is a weaker result proved by Gladysz before the full Newelski–Pawlikowski–
Seredyński theorem [NPS87]. -/
@[category research solved, AMS 5 28]
theorem erdos_501.variants.gladysz_size2 : answer(True) ↔
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, 2 ≤ X.ncard ∧ X.Pairwise (fun x y => x ∉ A y) := by
  simp only [true_iff]
  sorry

/--
**Trivial lower bound: a single-element set is always independent.**

For any family `A`, any singleton `{x}` is vacuously independent: there are no two
distinct elements. -/
@[category textbook, AMS 5 28]
theorem erdos_501.variants.singleton_independent (A : ℝ → Set ℝ) (x : ℝ) :
    ({x} : Set ℝ).Pairwise (fun x y => x ∉ A y) :=
  Set.pairwise_singleton x _

/--
**Two-element sets: independent iff mutual non-membership.**

A two-element set `{x, y}` (with `x ≠ y`) is independent for `A` if and only if
`x ∉ A y` and `y ∉ A x`. -/
@[category textbook, AMS 5 28]
theorem erdos_501.variants.pair_independent_iff (A : ℝ → Set ℝ) {x y : ℝ} (hxy : x ≠ y) :
    ({x, y} : Set ℝ).Pairwise (fun x y => x ∉ A y) ↔ x ∉ A y ∧ y ∉ A x := by
  rw [Set.pairwise_pair]
  exact ⟨fun h => h hxy, fun h _ => h⟩

/- ## Sanity checks and examples

The following `example` declarations exercise the proved variants and demonstrate that
the hypotheses of the main theorem are non-vacuous. All goals are fully closed: no `sorry`. -/

/-- The constant family `A x = ∅` satisfies all hypotheses of the main problem:
each `A x` is bounded (the empty set is bounded) and has Lebesgue outer measure 0 < 1.
Moreover, all of ℝ is an independent set, showing the conclusion holds trivially.

This demonstrates that the hypotheses are non-vacuous: the family `A x = ∅` is a valid
input to the theorem, and `ℝ` (which is infinite) witnesses the conclusion. -/
@[category test, AMS 5 28]
theorem erdos_501.tests.empty_family_is_valid :
    let A : ℝ → Set ℝ := fun _ => ∅
    (∀ x, Bornology.IsBounded (A x)) ∧
    (∀ x, volume.toOuterMeasure (A x) < 1) ∧
    ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  refine ⟨fun _ => Bornology.isBounded_empty, fun _ => ?_, Set.univ, Set.infinite_univ, ?_⟩
  · simp
  · intro x _ y _ _ hxAy; exact hxAy

/-- A singleton `{0}` is an independent set for any family `A : ℝ → Set ℝ`,
as witnessed by `erdos_501.variants.singleton_independent`. -/
@[category test, AMS 5 28]
theorem erdos_501.tests.singleton_zero_independent (A : ℝ → Set ℝ) :
    ({0} : Set ℝ).Pairwise (fun x y => x ∉ A y) :=
  erdos_501.variants.singleton_independent A 0

/-- Two reals form an independent set for the empty family `A _ = ∅`:
neither 0 nor 1 belongs to ∅, so both conditions of `pair_independent_iff` hold. -/
@[category test, AMS 5 28]
theorem erdos_501.tests.pair_independent_empty :
    ({0, 1} : Set ℝ).Pairwise (fun x y => x ∉ (fun _ => (∅ : Set ℝ)) y) := by
  rw [erdos_501.variants.pair_independent_iff _ (by norm_num : (0:ℝ) ≠ 1)]
  exact ⟨Set.notMem_empty _, Set.notMem_empty _⟩

/-- The hypothesis `volume.toOuterMeasure (A x) < 1` is strictly satisfied when
`A x = {x}` (a singleton), since Lebesgue measure of a singleton is 0. -/
@[category test, AMS 5 28]
theorem erdos_501.tests.singleton_outer_measure_lt_one (x : ℝ) :
    volume.toOuterMeasure ({x} : Set ℝ) < 1 := by
  simp [Measure.toOuterMeasure_apply]

/-- The boundary case: the measure condition `< 1` is sharp. An interval of length ≥ 1
has Lebesgue measure ≥ 1, so it would fail the hypothesis. Here `[0, 1]` has measure exactly 1. -/
@[category test, AMS 5 28]
theorem erdos_501.tests.unit_interval_measure :
    volume.toOuterMeasure (Set.Icc (0:ℝ) 1) = 1 := by
  simp [Measure.toOuterMeasure_apply, Real.volume_Icc]

end Erdos501
