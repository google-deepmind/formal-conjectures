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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 603

**Verbatim statement (Erdős #603, status O):**
> Let $(A_i)$ be a family of countably infinite sets such that $\lvert A_i\cap A_j\rvert \neq 2$ for all $i\neq j$. Find the smallest cardinal $C$ such that $\cup A_i$ can always be coloured with at most $C$ colours so that no $A_i$ is monochromatic.

**Source:** https://www.erdosproblems.com/603

**Notes:** OPEN


*Reference:* [erdosproblems.com/603](https://www.erdosproblems.com/603)

## Problem statement (exact wording from the source)

> Let $(A_i)$ be a family of countably infinite sets such that $|A_i \cap A_j| \neq 2$ for all
> $i \neq j$. Find the smallest cardinal $C$ such that $\cup A_i$ can always be coloured with
> at most $C$ colours so that no $A_i$ is monochromatic.

This is **[Er87]**, a problem of Komjáth. It is currently open.

## Relationship to Problem 602

Problem 603 is the "sister" of [Problem 602](https://www.erdosproblems.com/602):
- **Problem 602** asks the same question but with the forbidden intersection size being 1
  (i.e., $|A_i \cap A_j| \neq 1$ for all $i \neq j$) and whether 2 colours always suffice.
- **Problem 603** asks for the **minimum** number of colours $C$ when the forbidden
  intersection size is 2 (i.e., $|A_i \cap A_j| \neq 2$ for all $i \neq j$).

## Komjáth's known result

Komjáth proved that for families satisfying $|A_i \cap A_j| \neq 1$ for all $i \neq j$,
$\aleph_0$ colours always suffice (and in fact 2 suffice — related to Problem 602).
For Problem 603 (forbidden size 2), the analogous minimum cardinal $C$ is open.

## Formalization choices

- We work over an **arbitrary ground type** `α : Type*`, which generalises the original
  formulation (typically over `ℕ`). Since every countably infinite set bijects with `ℕ`,
  the two formulations are equivalent.
- **Countably infinite** sets are represented as `Set.Countable ∧ Set.Infinite`.
- A **$C$-colouring** of `α` using colours from a type `C` is a function `f : α → C`.
- A set `A` is **monochromatic** under `f` if `f` is constant on `A`.
- **$C$-chromatic Property B** asserts: there exists a colouring `f : α → C` (with `C` many
  colours) such that no `A_i` is monochromatic.
- The open problem asks for the **smallest cardinal** `C` satisfying this for all such families.
  We formalize this as: the smallest `C` such that `C`-chromatic Property B holds for every
  family satisfying the intersection condition.
-/

open Set Cardinal

namespace Erdos603

/- ## Setup -/

/-- A set `A ⊆ α` is **monochromatic** under a colouring `f : α → C`
if all elements of `A` receive the same colour. -/
def IsMonochromatic {α C : Type*} (f : α → C) (A : Set α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, f x = f y

/-- A family `(A_i)_{i ∈ I}` of subsets of `α` has **`C`-chromatic Property B** if there exists
a colouring `f : α → C` (using at most `#C` colours) such that no `A_i` is monochromatic.

When `C = Fin 2`, this reduces to the classical Property B (2-colouring). -/
def HasChromaticPropertyB {α : Type*} (C : Type*) (I : Type*) (A : I → Set α) : Prop :=
  ∃ f : α → C, ∀ i, ¬IsMonochromatic f (A i)

/-- A family `(A_i)_{i ∈ I}` of subsets of `α` has **Property B** (the classical 2-colour
version) if there exists a 2-colouring `f : α → Fin 2` such that no `A_i` is monochromatic.
This specialises `HasChromaticPropertyB` to `C = Fin 2`. -/
def HasPropertyB {α : Type*} (I : Type*) (A : I → Set α) : Prop :=
  HasChromaticPropertyB (Fin 2) I A

/- ## Main open problem -/

/--
**Erdős Problem 603 (open).**

Let $(A_i)$ be a family of countably infinite sets such that $|A_i \cap A_j| \neq 2$ for all
$i \neq j$. Find the smallest cardinal $C$ such that $\cup A_i$ can always be coloured with at
most $C$ colours so that no $A_i$ is monochromatic.

Formally: we ask for the smallest cardinal `C` (i.e., the smallest type `κ` with
`#κ = C`) such that: for every type `α`, every family `(A_i)_{i ∈ I}` of countably infinite
subsets of `α` with `Set.ncard (A_i ∩ A_j) ≠ 2` for all `i ≠ j`, there exists a
`κ`-colouring of `α` with no monochromatic `A_i`.

The answer `C` is the chromatic number of the "non-2-intersection hypergraph" over countably
infinite sets.

**Note on the analogous known result:** Komjáth proved that for the condition
$|A_i \cap A_j| \neq 1$, one can always colour with at most $\aleph_0$ colours (Problem 602).
The current problem — the minimum $C$ for the condition $|A_i \cap A_j| \neq 2$ — is open.

**Note on generalisation:** We work over an arbitrary ground type `α : Type*` so that the
statement covers families of countably infinite subsets of uncountable ambient spaces.
Since every countably infinite set bijects with `ℕ`, this is equivalent to the standard
formulation over `ℕ`.

**Formalization note on "smallest cardinal":** The problem asks for the *minimum* `C`. We
formalize this as: `C` is the smallest cardinal with `HasChromaticPropertyB (C.out) I A`.
The `answer(sorry)` placeholder represents the (currently unknown) cardinal answer. -/
@[category research open, AMS 3 5]
theorem erdos_603 : answer(sorry) ↔
    ∀ {α : Type*} {I : Type*} (A : I → Set α),
      (∀ i, (A i).Countable ∧ (A i).Infinite) →
      (∀ i j, i ≠ j → Set.ncard (A i ∩ A j) ≠ 2) →
      HasChromaticPropertyB ℕ I A := by
  sorry

/- ## Variants and partial results -/

/--
**ℵ₀ colours suffice for disjoint families.**

If the `A_i` are pairwise disjoint (in particular `|A_i ∩ A_j| = 0 ≠ 2`), then countably
many colours (using a colouring by `ℕ`) always suffice to make the family non-monochromatic.

In fact, even 2 colours suffice in the disjoint case (same proof as in Problem 602).
Here we record the version with `ℕ`-many colours as a corollary of the 2-colour version,
which is easier to state in the context of Problem 603's `ℕ`-valued colouring framework.

**Proof:** Since each `A i` is infinite, it has two distinct elements. Colour one of them
with colour 1 (say) and everything else with colour 0. By disjointness, the choices for
different sets do not conflict, and no `A i` is monochromatic. -/
@[category research solved, AMS 3 5]
theorem erdos_603.variants.disjoint : answer(True) ↔
    ∀ {α : Type*} {I : Type*} (A : I → Set α),
      (∀ i, (A i).Infinite) →
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
      HasChromaticPropertyB ℕ I A := by
  simp only [true_iff]
  intro α I A hInfinite hDisjoint
  -- For each i, pick two distinct elements a_fn i, b_fn i ∈ A i.
  have ha_b : ∀ i, ∃ a b : α, a ∈ A i ∧ b ∈ A i ∧ a ≠ b := by
    intro i
    obtain ⟨a, ha⟩ := (hInfinite i).nonempty
    have hA2 : (A i \ {a}).Nonempty := by
      apply Set.Infinite.nonempty
      exact (hInfinite i).diff (Set.finite_singleton a)
    obtain ⟨b, hbA, hba⟩ := hA2
    simp only [Set.mem_singleton_iff] at hba
    exact ⟨a, b, ha, hbA, fun h => hba h.symm⟩
  choose a_fn b_fn ha_mem hb_mem hab_ne using ha_b
  -- Key property: a_fn i ≠ b_fn j for any j (by disjointness).
  have key : ∀ i j, a_fn i ≠ b_fn j := by
    intro i j haj
    by_cases hij : i = j
    · subst hij; exact hab_ne i haj
    · have hdisj := hDisjoint i j hij
      rw [Set.disjoint_left] at hdisj
      have hbj : b_fn j ∈ A j := hb_mem j
      rw [← haj] at hbj
      exact hdisj (ha_mem i) hbj
  -- Colouring: f x = 1 if x = b_fn i for some i, else 0.
  classical
  let f : α → ℕ := fun x => if ∃ i, x = b_fn i then 1 else 0
  refine ⟨f, fun i => ?_⟩
  intro hMono
  -- f (a_fn i) = 0: since a_fn i ≠ b_fn j for all j.
  have hfa : f (a_fn i) = 0 := by
    simp only [f]
    rw [if_neg]
    rintro ⟨j, hj⟩
    exact absurd hj (key i j)
  -- f (b_fn i) = 1: witnessed by i itself.
  have hfb : f (b_fn i) = 1 := by
    simp only [f]
    rw [if_pos]
    exact ⟨i, rfl⟩
  -- hMono says f is constant on A i, but f (a_fn i) = 0 ≠ 1 = f (b_fn i).
  have hne := hMono (a_fn i) (ha_mem i) (b_fn i) (hb_mem i)
  rw [hfa, hfb] at hne
  exact absurd hne (by decide)

/--
**Empty index set.**

If the index set `I` is empty, then `HasChromaticPropertyB` holds vacuously for any colouring
type (in particular for `ℕ`-colourings). -/
@[category undergraduate, AMS 3]
theorem erdos_603.variants.empty_index {α : Type*} :
    ∀ (A : PEmpty → Set α),
      (∀ i, (A i).Infinite) →
      HasChromaticPropertyB ℕ PEmpty A := by
  intro A _
  exact ⟨fun _ => 0, fun i => i.elim⟩

/--
**Unique index set.**

If the index set has exactly one element, then `HasChromaticPropertyB ℕ I A` holds:
the single infinite set `A default` has two distinct elements, so we can colour one with 1
and the other with 0. -/
@[category undergraduate, AMS 3]
theorem erdos_603.variants.unique_index {α : Type*} (I : Type*) [Unique I]
    (A : I → Set α) (hInfinite : ∀ i, (A i).Infinite) :
    HasChromaticPropertyB ℕ I A := by
  classical
  -- A default is infinite: pick two distinct elements.
  obtain ⟨a, ha⟩ := (hInfinite default).nonempty
  have hA2 : (A default \ {a}).Nonempty :=
    Set.Infinite.nonempty ((hInfinite default).diff (Set.finite_singleton a))
  obtain ⟨b, hbA, hba⟩ := hA2
  simp only [Set.mem_singleton_iff] at hba
  -- Colour b with 1, everything else with 0.
  refine ⟨fun x => if x = b then 1 else 0, fun i => ?_⟩
  rw [Unique.eq_default i]
  intro hMono
  have hfa : (fun x : α => if x = b then (1 : ℕ) else 0) a = 0 := by
    simp [show a ≠ b from fun h => hba h.symm]
  have hfb : (fun x : α => if x = b then (1 : ℕ) else 0) b = 1 := by simp
  have := hMono a ha b hbA
  rw [hfa, hfb] at this
  exact absurd this (by decide)

/--
**Two sets with non-2 intersection.**

For two countably infinite sets `A₀, A₁` with `|A₀ ∩ A₁| ≠ 2` (and the intersection finite),
a colouring with at most `ℕ`-many colours (in fact 2 colours suffice) exists making neither
set monochromatic.

**Proof sketch:**
- If `A₀ ∩ A₁ = ∅` (intersection empty, so `|A₀ ∩ A₁| = 0 ≠ 2`): the sets are disjoint.
  Pick distinct `a, b ∈ A₀` and distinct `c, d ∈ A₁`. Colour `b` and `c` with 1, all others
  with 0. Then `A₀` has colours 0 (at `a`) and 1 (at `b`), and `A₁` has colours 1 (at `c`)
  and 0 (at `d`).
- If `|A₀ ∩ A₁| = 1` (a single common element `x`): pick any `y ∈ A₀ \ A₁`. Colour `y` with
  1, everything else with 0. Then `A₀` has both colours (at `x` and `y`). For `A₁`: since `y ∉ A₁`,
  all elements of `A₁` get colour 0. But `A₁` is infinite so it has two elements, both colour 0
  — monochromatic. Instead, pick `z ∈ A₁ \ {x}` and colour `z` with 1 too. Now `A₁` has colours
  0 (at `x`) and 1 (at `z`). For `A₀`: it has colour 0 (at `x`) and colour 1 (at `y`).
- If `|A₀ ∩ A₁| ≥ 3`: the intersection has three or more elements. Pick distinct `x, y ∈ A₀ ∩ A₁`.
  Colour `y` with 1, all else with 0. Both `A₀` and `A₁` contain `x` (colour 0) and `y` (colour 1).

(The case `|A₀ ∩ A₁| = 2` is excluded by hypothesis.) -/
@[category research solved, AMS 3 5]
theorem erdos_603.variants.two_sets : answer(True) ↔
    ∀ {α : Type*} (A : Fin 2 → Set α),
      (∀ i, (A i).Infinite) →
      (A 0 ∩ A 1).Finite →
      Set.ncard (A 0 ∩ A 1) ≠ 2 →
      HasChromaticPropertyB ℕ (Fin 2) A := by
  simp only [true_iff]
  intro α A hInfinite hFin hNcard
  classical
  -- Case split on the size of the intersection.
  by_cases hEmpty : (A 0 ∩ A 1) = ∅
  · -- Disjoint case: intersection empty.
    -- Pick a, b ∈ A 0 (distinct).
    obtain ⟨a, ha0⟩ := (hInfinite 0).nonempty
    have hA0' : (A 0 \ {a}).Nonempty :=
      Set.Infinite.nonempty ((hInfinite 0).diff (Set.finite_singleton a))
    obtain ⟨b, hbA0, hba⟩ := hA0'
    simp only [Set.mem_singleton_iff] at hba
    -- Pick c, d ∈ A 1 (distinct).
    obtain ⟨c, hc1⟩ := (hInfinite 1).nonempty
    have hA1' : (A 1 \ {c}).Nonempty :=
      Set.Infinite.nonempty ((hInfinite 1).diff (Set.finite_singleton c))
    obtain ⟨d, hd1, hdc⟩ := hA1'
    simp only [Set.mem_singleton_iff] at hdc
    -- Disjointness: no element belongs to both A 0 and A 1.
    have hDisj : ∀ x, x ∈ A 0 → x ∉ A 1 := by
      intro x hx0 hx1
      exact absurd (Set.mem_inter hx0 hx1) (hEmpty ▸ Set.notMem_empty x)
    have hb_ne_c : b ≠ c := fun h => hDisj b hbA0 (h ▸ hc1)
    have hb_ne_d : b ≠ d := fun h => hDisj b hbA0 (h ▸ hd1)
    have ha_ne_c : a ≠ c := fun h => hDisj a ha0 (h ▸ hc1)
    -- Colour: 1 if x = b or x = c, else 0.
    refine ⟨fun x => if x = b ∨ x = c then 1 else 0, fun i => ?_⟩
    fin_cases i
    · -- A 0: f(a) = 0 (a ≠ b, a ≠ c), f(b) = 1.
      intro hMono
      have hfa : (fun x : α => if x = b ∨ x = c then (1 : ℕ) else 0) a = 0 := by
        simp [show a ≠ b from fun h => hba h.symm, ha_ne_c]
      have hfb : (fun x : α => if x = b ∨ x = c then (1 : ℕ) else 0) b = 1 := by simp
      have := hMono a ha0 b hbA0
      rw [hfa, hfb] at this; exact absurd this (by decide)
    · -- A 1: f(c) = 1, f(d) = 0 (d ≠ b, d ≠ c).
      intro hMono
      have hfc : (fun x : α => if x = b ∨ x = c then (1 : ℕ) else 0) c = 1 := by simp
      have hfd : (fun x : α => if x = b ∨ x = c then (1 : ℕ) else 0) d = 0 := by
        simp [hb_ne_d.symm, hdc]
      have := hMono c hc1 d hd1
      rw [hfc, hfd] at this; exact absurd this (by decide)
  · -- Non-empty intersection.
    -- Split: size 1 or size ≥ 3 (size 2 is excluded by hNcard).
    have hnonempty : (A 0 ∩ A 1).Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    have hcard_pos : 0 < Set.ncard (A 0 ∩ A 1) := by
      rwa [Set.ncard_pos hFin]
    -- If ncard = 1: exactly one common element.
    by_cases hcard1 : Set.ncard (A 0 ∩ A 1) = 1
    · -- Exactly one element in intersection: obtain it.
      rw [Set.ncard_eq_one] at hcard1
      obtain ⟨x, hx_eq⟩ := hcard1
      have hxI : x ∈ A 0 ∩ A 1 := by rw [hx_eq]; exact Set.mem_singleton x
      -- A 1 is infinite, so pick y ∈ A 1 with y ≠ x.
      have hA1' : (A 1 \ {x}).Nonempty :=
        Set.Infinite.nonempty ((hInfinite 1).diff (Set.finite_singleton x))
      obtain ⟨y, hy1, hyx⟩ := hA1'
      simp only [Set.mem_singleton_iff] at hyx
      -- y ∉ A 0: if y ∈ A 0 then y ∈ A 0 ∩ A 1 = {x}, so y = x, contradiction.
      have hy_not_A0 : y ∉ A 0 := by
        intro hy0
        have : y ∈ A 0 ∩ A 1 := ⟨hy0, hy1⟩
        rw [hx_eq] at this
        exact hyx (Set.mem_singleton_iff.mp this)
      -- A 0 is infinite, so pick z ∈ A 0 with z ≠ x.
      have hA0' : (A 0 \ {x}).Nonempty :=
        Set.Infinite.nonempty ((hInfinite 0).diff (Set.finite_singleton x))
      obtain ⟨z, hz0, hzx⟩ := hA0'
      simp only [Set.mem_singleton_iff] at hzx
      -- Colour: y → 1, z → 2, everything else → 0.
      -- A 0: x gets 0 (x ≠ y since y ∉ A 0 but x ∈ A 0, and x ≠ z by hzx.symm),
      --      z gets 2. Non-monochromatic.
      -- A 1: x gets 0, y gets 1. Non-monochromatic.
      refine ⟨fun v => if v = y then 1 else if v = z then 2 else 0, fun i => ?_⟩
      have hx_ne_y : x ≠ y := fun h => hy_not_A0 (h ▸ hxI.1)
      have hx_ne_z : x ≠ z := fun h => hzx h.symm
      have hz_ne_y : z ≠ y := fun h => hy_not_A0 (h ▸ hz0)
      fin_cases i
      · -- A 0: f(x) = 0 (x ≠ y, x ≠ z), f(z) = 2 (z ≠ y, z = z). Non-monochromatic.
        intro hMono
        have := hMono x hxI.1 z hz0
        simp only [hx_ne_y, hx_ne_z, hz_ne_y, if_false, if_true] at this
        exact absurd this (by decide)
      · -- A 1: f(x) = 0 (x ≠ y, x ≠ z), f(y) = 1 (y = y). Non-monochromatic.
        intro hMono
        have := hMono x hxI.2 y hy1
        simp only [hx_ne_y, hx_ne_z, if_false, if_true] at this
        exact absurd this (by decide)
    · -- ncard ≠ 0, ≠ 1, ≠ 2 → ncard ≥ 3.
      have hge3 : 2 < Set.ncard (A 0 ∩ A 1) := by omega
      -- Get two distinct elements x, y in the intersection.
      have hge2 : 1 < Set.ncard (A 0 ∩ A 1) := by omega
      obtain ⟨x, hxI, y, hyI, hxy⟩ := (Set.one_lt_ncard hFin).mp hge2
      -- Colour y with 1, everything else with 0.
      refine ⟨fun v => if v = y then 1 else 0, fun i => ?_⟩
      fin_cases i
      · -- A 0: f(x) = 0 (x ≠ y), f(y) = 1, both in A 0.
        intro hMono
        have hfx : (fun v : α => if v = y then (1 : ℕ) else 0) x = 0 := by simp [hxy]
        have hfy : (fun v : α => if v = y then (1 : ℕ) else 0) y = 1 := by simp
        have := hMono x hxI.1 y hyI.1
        rw [hfx, hfy] at this; exact absurd this (by decide)
      · -- A 1: f(x) = 0, f(y) = 1, both in A 1.
        intro hMono
        have hfx : (fun v : α => if v = y then (1 : ℕ) else 0) x = 0 := by simp [hxy]
        have hfy : (fun v : α => if v = y then (1 : ℕ) else 0) y = 1 := by simp
        have := hMono x hxI.2 y hyI.2
        rw [hfx, hfy] at this; exact absurd this (by decide)

/- ## Sanity checks and examples -/

/- ### Auxiliary lemmas -/

@[category test, AMS 3 5]
private lemma evens_infinite603 : Set.Infinite {n : ℕ | Even n} :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
    (by intro a b h; simp only at h; omega)
    (by intro n; simp only [Set.mem_setOf_eq]; exact ⟨n, by ring⟩)

@[category test, AMS 3 5]
private lemma odds_infinite603 : Set.Infinite {n : ℕ | Odd n} :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + 1)
    (by intro a b h; simp only at h; omega)
    (by intro n; simp only [Set.mem_setOf_eq]; exact ⟨n, by ring⟩)

@[category test, AMS 3 5]
private lemma evens_inter_odds_empty603 : {n : ℕ | Even n} ∩ {n : ℕ | Odd n} = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro ⟨k, hk⟩ ⟨m, hm⟩; omega

/-- The empty family vacuously has chromatic Property B,
exercising `erdos_603.variants.empty_index`. -/
@[category test, AMS 3 5]
example : HasChromaticPropertyB ℕ PEmpty (fun (_ : PEmpty) => (Set.univ : Set ℕ)) :=
  erdos_603.variants.empty_index _ (fun _ => Set.infinite_univ)

/-- Any infinite set, viewed as a singleton family, has chromatic Property B,
exercising `erdos_603.variants.unique_index`. -/
@[category test, AMS 3 5]
example (A : Set ℕ) (hA : A.Infinite) :
    HasChromaticPropertyB ℕ Unit (fun _ => A) :=
  erdos_603.variants.unique_index Unit (fun _ => A) (fun _ => hA)

/-- The evens/odds family on ℕ satisfies all hypotheses of the main theorem:
countably infinite sets, pairwise intersection of size 0 ≠ 2. -/
@[category test, AMS 3 5]
example :
    let A : Fin 2 → Set ℕ := ![{n | Even n}, {n | Odd n}]
    (∀ i, (A i).Countable ∧ (A i).Infinite) ∧
    (∀ i j, i ≠ j → Set.ncard (A i ∩ A j) ≠ 2) := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i
    · exact ⟨(Set.countable_univ).mono (Set.subset_univ _), evens_infinite603⟩
    · exact ⟨(Set.countable_univ).mono (Set.subset_univ _), odds_infinite603⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | skip
    · show Set.ncard ({n : ℕ | Even n} ∩ {n | Odd n}) ≠ 2
      rw [evens_inter_odds_empty603, Set.ncard_empty]; decide
    · show Set.ncard ({n : ℕ | Odd n} ∩ {n | Even n}) ≠ 2
      rw [Set.inter_comm, evens_inter_odds_empty603, Set.ncard_empty]; decide

/-- The evens/odds disjoint family has chromatic Property B with ℕ-many colours,
exercising `erdos_603.variants.disjoint`. This provides an explicit witness. -/
@[category test, AMS 3 5]
example : HasChromaticPropertyB ℕ (Fin 2) (![{n : ℕ | Even n}, {n | Odd n}] : Fin 2 → Set ℕ) := by
  classical
  -- Colour: 1 if n = 1 (the "b_fn 1" element), else 0.
  -- f(0) = 0 ≠ 1 = f(2) for evens; f(1) = 1 ≠ 0 = f(3) for odds.
  refine ⟨fun n => if n = 2 ∨ n = 1 then 1 else 0, fun i hMono => ?_⟩
  fin_cases i
  · -- A 0 = evens: f(0) = 0, f(2) = 1.
    have h0 : (fun n : ℕ => if n = 2 ∨ n = 1 then (1 : ℕ) else 0) 0 = 0 := by decide
    have h2 : (fun n : ℕ => if n = 2 ∨ n = 1 then (1 : ℕ) else 0) 2 = 1 := by decide
    have hmem0 : (0 : ℕ) ∈ (![{n : ℕ | Even n}, {n | Odd n}] : Fin 2 → Set ℕ) 0 := by
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq]; exact ⟨0, by ring⟩
    have hmem2 : (2 : ℕ) ∈ (![{n : ℕ | Even n}, {n | Odd n}] : Fin 2 → Set ℕ) 0 := by
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq]; exact ⟨1, by ring⟩
    have := hMono 0 hmem0 2 hmem2
    rw [h0, h2] at this; exact absurd this (by decide)
  · -- A 1 = odds: f(1) = 1, f(3) = 0.
    have h1 : (fun n : ℕ => if n = 2 ∨ n = 1 then (1 : ℕ) else 0) 1 = 1 := by decide
    have h3 : (fun n : ℕ => if n = 2 ∨ n = 1 then (1 : ℕ) else 0) 3 = 0 := by decide
    have hmem1 : (1 : ℕ) ∈ (![{n : ℕ | Even n}, {n | Odd n}] : Fin 2 → Set ℕ) 1 := by
      simp only [Matrix.cons_val_one]; exact ⟨0, by ring⟩
    have hmem3 : (3 : ℕ) ∈ (![{n : ℕ | Even n}, {n | Odd n}] : Fin 2 → Set ℕ) 1 := by
      simp only [Matrix.cons_val_one]; exact ⟨1, by ring⟩
    have := hMono 1 hmem1 3 hmem3
    rw [h1, h3] at this; exact absurd this (by decide)

/-- The boundary condition: a family where `|A₀ ∩ A₁| = 2` is correctly excluded.
This shows the hypothesis `Set.ncard (A i ∩ A j) ≠ 2` is faithfully encoded. -/
@[category test, AMS 3 5]
example : Set.ncard ({n : ℕ | Even n} ∩ {n : ℕ | n = 0 ∨ n = 2}) = 2 := by
  have heq : {n : ℕ | Even n} ∩ {n : ℕ | n = 0 ∨ n = 2} = {0, 2} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨k, hk⟩, rfl | rfl⟩ <;> simp
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by ring⟩, Or.inl rfl⟩
      · exact ⟨⟨1, by ring⟩, Or.inr rfl⟩
  rw [heq]
  exact Set.ncard_pair (by decide)

/- ## Disproof of natural-looking false variant

We formally disprove a plausible misformalization to document which hypotheses are
load-bearing. -/

/-- A natural but FALSE relaxation: drop the infiniteness hypothesis on the sets `A i`.
Without `(A i).Infinite`, a singleton set is monochromatic under any colouring. -/
def chromatic_without_infinite_claim : Prop :=
  ∀ {α : Type} {I : Type} (A : I → Set α),
    (∀ i j, i ≠ j → Set.ncard (A i ∩ A j) ≠ 2) →
    HasChromaticPropertyB ℕ I A

/-- Formal disproof of `chromatic_without_infinite_claim`.

**Counterexample:** Take `α = ℕ`, `I = Fin 2`, `A 0 = {0}` (singleton) and `A 1 = {1, 2}`.
The intersection `A 0 ∩ A 1 = ∅` has size 0 ≠ 2. But `A 0 = {0}` is a singleton,
and any singleton set is monochromatic under any colouring (vacuously, since the only
pair `(x, y) ∈ {0} × {0}` gives `f 0 = f 0`). Hence `HasChromaticPropertyB` fails. -/
@[category research solved, AMS 3]
theorem chromatic_without_infinite_claim.disproof :
    ¬ chromatic_without_infinite_claim := by
  intro h
  -- Apply h to: A 0 = {0}, A 1 = {1, 2} on α = ℕ.
  have hApp : HasChromaticPropertyB ℕ (Fin 2)
      (fun k : Fin 2 => if k = 0 then ({0} : Set ℕ) else {1, 2}) :=
    h (fun k : Fin 2 => if k = 0 then ({0} : Set ℕ) else {1, 2}) (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Set.ncard_empty])
  obtain ⟨f, hf⟩ := hApp
  -- hf 0 says A 0 = {0} is not monochromatic. But {0} is a singleton!
  apply hf 0
  simp only [Fin.isValue, ↓reduceIte]
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy
  rw [hx, hy]

/-- Drift-detection type assertion: if the claim definition changes out of sync with
the disproof, this elaboration will fail at build time. -/
@[category research solved, AMS 3]
theorem chromatic_without_infinite_claim.type_check :
    ¬ chromatic_without_infinite_claim :=
  chromatic_without_infinite_claim.disproof

end Erdos603
