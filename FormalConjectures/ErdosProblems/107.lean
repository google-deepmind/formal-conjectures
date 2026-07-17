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

import FormalConjecturesUtil

/-!
# Erdős Problem 107

*References:*
- [erdosproblems.com/107](https://www.erdosproblems.com/107)
- [Wikipedia](https://en.wikipedia.org/wiki/Happy_ending_problem)
-/

open Filter
open EuclideanGeometry

namespace Erdos107

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain a convex $n$-gon. -/
def cardSet (n : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
  HasConvexNGon n pts }

/-- The function $f(n)$ specified in `erdos_107`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

/--
Let $f(n)$ be minimal such that any $f(n)$ points in $ℝ^2$, no three on a line,
contain $n$ points which form the vertices of a convex $n$-gon.
Prove that $f(n) = 2^{n-2} + 1$.
-/
@[category research open, AMS 52]
theorem erdos_107 : answer(sorry) ↔ ∀ n ≥ 3, f n = 2^(n - 2) + 1 := by
  sorry

/-- For every $n ≥ 3$, there exists $N$ such that any $N$ points, no three on a line,
contain a convex $n$-gon. -/
@[category research solved, AMS 52]
theorem nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty := by
  sorry

/-- Depending on details of definitions,
the statement is false or trivial for $n < 3$. -/
@[category test, AMS 52]
theorem f_zero_eq : f 0 = 0 := by
  have : ∀ P, HasConvexNGon 0 P := by
    intro; use ∅; simp [ConvexIndep]
  simp [f, cardSet, this]

/-- Three distinct non-collinear points form a convex-independent set. -/
@[category API, AMS 52]
private lemma convexIndep_triple_of_not_collinear {a b c : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    ConvexIndep ({a, b, c} : Set ℝ²) := by
  intro x hx hmem
  -- The point `x` lies in the affine span of `{a, b, c} \ {x}` because it
  -- lies in the convex hull of that two-element set.
  apply hcoll
  have hx_aff : x ∈ affineSpan ℝ (({a, b, c} : Set ℝ²) \ {x}) :=
    convexHull_subset_affineSpan _ hmem
  rw [show ({a, b, c} : Set ℝ²) = insert x (({a, b, c} : Set ℝ²) \ {x}) from
        (Set.insert_diff_self_of_mem hx).symm,
      collinear_insert_iff_of_mem_affineSpan hx_aff]
  -- The two-element complement is collinear.
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [show ({x, b, c} : Set ℝ²) \ {x} = ({b, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ b c
  · rw [show ({a, x, c} : Set ℝ²) \ {x} = ({a, c} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a c
  · rw [show ({a, b, x} : Set ℝ²) \ {x} = ({a, b} : Set ℝ²) by ext; aesop]
    exact collinear_pair ℝ a b

@[category test, AMS 52]
theorem f_three_eq : f 3 = 3 := by
  -- The substantive bound: 3 ∈ cardSet 3.
  have hmem3 : (3 : ℕ) ∈ cardSet 3 := by
    intro pts hpts hnontri
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hpts
    refine ⟨{a, b, c}, by simp [hab, hac, hbc], subset_refl _, ?_⟩
    have hcoerce : (({a, b, c} : Finset ℝ²) : Set ℝ²) = ({a, b, c} : Set ℝ²) := by simp
    have hmem : ∀ {y : ℝ²}, y ∈ ({a, b, c} : Set ℝ²) →
        y ∈ (({a, b, c} : Finset ℝ²) : Set ℝ²) := fun h => hcoerce ▸ h
    have hnc : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
      hnontri (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) hab hbc hac
    rw [hcoerce]
    exact convexIndep_triple_of_not_collinear hab hac hbc hnc
  refine le_antisymm (Nat.sInf_le hmem3) (le_csInf ⟨3, hmem3⟩ fun N hN => ?_)
  -- A set with fewer than 3 points contains no 3-element subset.
  by_contra! hlt
  let f : ℕ → ℝ² := fun i => EuclideanSpace.single 0 (i : ℝ)
  let pts : Finset ℝ² := (Finset.range N).image f
  have hinj : Function.Injective f := fun i j hij => by
    have := congrArg (fun v : ℝ² => v 0) hij; simpa [f] using this
  have hpts_card : pts.card = N := by
    simp [pts, Finset.card_image_of_injOn hinj.injOn]
  have hnontri : NonTrilinear (pts : Set ℝ²) := by
    apply Set.triplewise_of_encard_lt
    rw [Set.encard_coe_eq_coe_finsetCard, hpts_card]
    exact_mod_cast hlt
  obtain ⟨S, hScard, hSsub, _⟩ := hN pts hpts_card hnontri
  have : S.card ≤ pts.card := Finset.card_le_card (by exact_mod_cast hSsub)
  omega

namespace variants

/--
Erdős and Szekeres proved the bounds
$$
  2^{n-2} + 1 ≤ f(n) ≤ \binom{2n-4}{n-2} + 1
$$
([ErSz60] and [ErSz35] respectively).

[ErSz60] Erdős, P. and Szekeres, G., _On some extremum problems in elementary geometry_.
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. (1960/61), 53-62.

[ErSz35] Erdős, P. and Szekeres, G., _A combinatorial problem in geometry_.
  Compos. Math. (1935), 463-470.
-/
@[category research solved, AMS 52]
theorem ersz_bounds :
    ∀ n ≥ 3, 2^(n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  sorry

/--
Suk [Su17] proved
$$
  f(n) ≤ 2^{(1+o(1))n}.
$$

[Su17] Suk, Andrew, _On the Erdős-Szekeres convex polygon problem_.
  J. Amer. Math. Soc. (2017), 1047-1053.
-/
@[category research solved, AMS 52]
theorem su_bound :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n ≥ 3, (f n : ℝ) ≤ 2^(n + r n) := by
  sorry

/--
The current best bound is due to Holmsen, Mojarrad, Pach, and Tardos [HMPT20],
who prove
$$
  f(n) ≤ 2^{n+O(\sqrt{n\log n})}.
$$

[HMPT20] Holmsen, Andreas F. and Mojarrad, Hossein Nassajian and Pach, János and Tardos, Gábor,
  _Two extensions of the Erdős-Szekeres problem_. J. Eur. Math. Soc. (JEMS) (2020), 3981-3995.
-/
@[category research solved, AMS 52]
theorem hmpt_bound :
    ∃ r : ℕ → ℝ, r =O[atTop] (fun n => Real.sqrt (n * Real.log n)) ∧
      ∀ n ≥ 3, (f n : ℝ) ≤ 2^(n + r n) := by
  sorry

end Erdos107.variants
