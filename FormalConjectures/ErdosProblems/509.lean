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
# Erdős Problem 509

*Reference:* [erdosproblems.com/509](https://www.erdosproblems.com/509)
-/

open Polynomial
open scoped Real

section BoundedDiscCover

universe u v

variable {M : Type u} [MetricSpace M]

/--An $r$-bounded disc cover of a subset of a metric space $M$
is an indexed family of closed discs whose radii sum to at most $r$.-/
structure BoundedDiscCover (S : Set M) (r : ℝ) (ι : Type v) where
  (C : ι → M)
  (R : ι → ℝ)
  (h_cover : S ⊆ ⋃ (i : ι), Metric.closedBall (C i) (R i))
  (h_summable : Summable (fun i : ι => R i))
  (h_bdd : ∑' i, R i ≤ r)
  (h_pos : ∀ i, 0 < R i)

variable (S : Set M) (r : ℝ)

noncomputable def boundedDiscCover_empty [Nonempty M] (r : ℝ) (hr : 0 < r) :
  (BoundedDiscCover (∅ : Set M) r (PUnit : Type v)) where
  C := fun _ => Classical.ofNonempty
  R := fun _ => r
  h_cover := Set.empty_subset _
  h_summable := (hasSum_fintype _).summable
  h_bdd := by
    have := hasSum_fintype fun (_ : (PUnit : Type v)) => if 0 ≤ r then -1 else r
    simp only [tsum_const, Nat.card_eq_fintype_card, Fintype.card_ofSubsingleton, smul_ite,
      smul_neg, one_smul, ge_iff_le]
    bound
  h_pos := by aesop

@[category API, AMS 54]
lemma BoundedDiscCover.bound_nonneg_of_nonempty
    (S : Set M) (hS : S.Nonempty) (r : ℝ) (ι : Type v)
    (bdc : BoundedDiscCover S r ι) :
    0 < r := by
  apply lt_of_lt_of_le _ bdc.h_bdd
  suffices Nonempty ι by
    apply tsum_pos bdc.h_summable (fun j => le_of_lt (bdc.h_pos j)) Classical.ofNonempty (bdc.h_pos _)
  by_contra!
  apply Set.Nonempty.ne_empty hS (Set.eq_empty_of_subset_empty _)
  convert bdc.h_cover
  aesop

end BoundedDiscCover

/--
Let $f(z) ∈ ℂ[z]$ be a monic non-constant polynomial. Can the set
$\{z ∈ ℂ : |f(z)| ≤ 1\}$
be covered by a set of closed discs the sum of whose radii is $≤ 2$?
-/
@[category research open, AMS 30]
theorem erdos_509 : (∀ (f : ℂ[X]), f.Monic → f.natDegree ≠ 0 →
    ∃ (ι : Type), Nonempty (BoundedDiscCover {z | ‖f.eval z‖ ≤ 1} 2 ι)) ↔ answer(sorry) := by
  sorry

/--
Let $f(z) ∈ ℂ[z]$ be a monic non-constant polynomial. Can the set
$\{z ∈ ℂ : |f(z)| ≤ 1\}$
be covered by a set of closed discs the sum of whose radii is ≤2e?
Solution: True. This is due to Cartan.
See *Sur les systèmes de fonctions holomorphes à variétés linéaires
lacunaires et leurs applications*, Henri Cartan,
http://www.numdam.org/article/ASENS_1928_3_45__255_0.pdf
-/
@[category research solved, AMS 30]
theorem erdos_509.variants.Cartan_bound : (∀ (f : ℂ[X]), f.Monic → f.natDegree ≠ 0 →
    ∃ (ι : Type), Nonempty (BoundedDiscCover {z | ‖f.eval z‖ ≤ 1} (2*rexp 1) ι)) ↔ answer(True) := by
  sorry

/--
Let $f(z) ∈ ℂ[z]$ be a monic non-constant polynomial. Can the set
$\{z ∈ ℂ : |f(z)| ≤ 1\}$
be covered by a set of closed discs the sum of whose radii is $≤ 2.59$?
Solution: True. This is due to Pommerenke.
-/
@[category research solved, AMS 30]
theorem erdos_509.variants.Pommerenke_bound : (∀ (f : ℂ[X]), f.Monic → f.natDegree ≠ 0 →
    ∃ (ι : Type), Nonempty (BoundedDiscCover {z | ‖f.eval z‖ ≤ 1} 2.59 ι)) ↔ answer(True) := by
  sorry

/--
Let $f(z) ∈ ℂ[z]$ be a monic non-constant polynomial.
If it is connected, can the set $\{z ∈ C : |f(z)| ≤ 1\}$
be covered by a set of circles the sum of whose radii is $≤ 2$?
Solution: True. This is due to Pommerenke.
-/
@[category research solved, AMS 30]
theorem erdos_509.variants.Pommerenke_connected : (∀ (f : ℂ[X]), f.Monic → f.natDegree ≠ 0 →
    IsConnected {z | ‖f.eval z‖ ≤ 1} →
    ∃ (ι : Type), Nonempty (BoundedDiscCover {z | ‖f.eval z‖ ≤ 1} 2 ι)) ↔ answer(True) := by
  sorry
