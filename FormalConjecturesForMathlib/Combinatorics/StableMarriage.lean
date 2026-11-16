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

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

/-!
# Stable marriage

A minimal finite model of the stable marriage problem with complete strict preferences.

For admissibility constraints, see
[Pittel, On Constrained Matchings](https://doi.org/10.1002/rsa.70036).
-/

namespace StableMarriage

/-- A preference profile for `n` men and `n` women. Each permutation maps a candidate to their
rank, with lower ranks preferred. -/
structure Profile (n : ℕ) where
  /-- The rank that each man assigns to each woman. -/
  manRank : Fin n → Equiv.Perm (Fin n)
  /-- The rank that each woman assigns to each man. -/
  womanRank : Fin n → Equiv.Perm (Fin n)
  deriving Inhabited

/-- Preference profiles form a finite type. -/
instance {n : ℕ} : Fintype (Profile n) :=
  Fintype.ofEquiv
    ((Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n)))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => (p.manRank, p.womanRank)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A complete matching of `n` men to `n` women. -/
abbrev Matching (n : ℕ) := Equiv.Perm (Fin n)

/-- A man and woman form a blocking pair when they are not matched to each other and each ranks
the other above their current partner. -/
def IsBlockingPair {n : ℕ} (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  μ m ≠ w ∧
    p.manRank m w < p.manRank m (μ m) ∧
      p.womanRank w m < p.womanRank w (μ.symm w)

/-- A matching is stable when it has no blocking pair. -/
def IsStable {n : ℕ} (p : Profile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ IsBlockingPair p μ m w

/-- The number of stable complete matchings for a preference profile. -/
noncomputable def numStableMatchings {n : ℕ} (p : Profile n) : ℕ := by
  classical
  exact Fintype.card {μ : Matching n // IsStable p μ}

/-- The discrete measurable structure on preference profiles. -/
instance {n : ℕ} : MeasurableSpace (Profile n) := ⊤

/-- The uniform probability mass function on preference profiles. -/
noncomputable def uniformProfile (n : ℕ) : PMF (Profile n) :=
  PMF.uniformOfFintype (Profile n)

/-- The expected number of stable matchings under the uniform profile distribution. -/
noncomputable def expectedNumStableMatchings (n : ℕ) : ℝ :=
  ∫ p, (numStableMatchings p : ℝ) ∂((uniformProfile n).toMeasure)

/-- A mask indicating which pairs may be matched. -/
abbrev Admissibility (n : ℕ) := (Fin n × Fin n) → Bool

/-- The mask that admits every pair. -/
def Admissibility.all (n : ℕ) : Admissibility n := fun _ ↦ true

/-- Each pair is admitted independently with probability `p`. -/
noncomputable def Admissibility.law (n : ℕ) (p : Set.Icc (0 : ℝ) 1) :
    MeasureTheory.Measure (Admissibility n) :=
  MeasureTheory.Measure.pi fun _ ↦ ProbabilityTheory.bernoulliMeasure true false p

instance (n : ℕ) (p : Set.Icc (0 : ℝ) 1) :
    MeasureTheory.IsProbabilityMeasure (Admissibility.law n p) := by
  unfold Admissibility.law
  infer_instance

/-- At probability one, every pair is admissible almost surely. -/
@[simp]
theorem Admissibility.law_one (n : ℕ) :
    law n 1 = MeasureTheory.Measure.dirac (all n) := by
  classical
  unfold law
  refine MeasureTheory.Measure.pi_eq fun s _ ↦ ?_
  simp [all, ProbabilityTheory.bernoulliMeasure_one, MeasureTheory.Measure.dirac_apply,
    Set.indicator_apply, Fintype.prod_ite_zero, Set.mem_pi]

/-- A partial matching is a set of pairs in which each participant appears at most once. -/
@[ext]
structure PartialMatching (n : ℕ) where
  /-- The pairs in the matching. -/
  pairs : Finset (Fin n × Fin n)
  /-- Each man has at most one partner. -/
  left_inj : Set.InjOn Prod.fst (pairs : Set (Fin n × Fin n))
  /-- Each woman has at most one partner. -/
  right_inj : Set.InjOn Prod.snd (pairs : Set (Fin n × Fin n))

/-- The partial matching consisting of the pairs of a complete matching. -/
def Matching.toPartialMatching {n : ℕ} (μ : Matching n) : PartialMatching n where
  pairs := Finset.univ.map ⟨fun m ↦ (m, μ m), fun _ _ h ↦ congrArg Prod.fst h⟩
  left_inj := by
    intro a ha b hb h
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨m', -, rfl⟩ := Finset.mem_map.mp hb
    exact congrArg (fun i ↦ (i, μ i)) h
  right_inj := by
    intro a ha b hb h
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨m', -, rfl⟩ := Finset.mem_map.mp hb
    exact congrArg (fun i ↦ (i, μ i)) (μ.injective h)

@[simp]
theorem mem_toPartialMatching_pairs {n : ℕ} (μ : Matching n) (m w : Fin n) :
    (m, w) ∈ μ.toPartialMatching.pairs ↔ μ m = w := by
  simp only [Matching.toPartialMatching, Finset.mem_map, Finset.mem_univ, true_and]
  change (∃ i, (i, μ i) = (m, w)) ↔ μ m = w
  simp

/-- An admissible pair blocks a partial matching if each participant is unmatched or prefers
the other to their current partner. -/
def IsPartialBlockingPair {n : ℕ} (p : Profile n) (A : Admissibility n)
    (M : PartialMatching n) (m w : Fin n) : Prop :=
  A (m, w) ∧
    (∀ w', (m, w') ∈ M.pairs → p.manRank m w < p.manRank m w') ∧
    (∀ m', (m', w) ∈ M.pairs → p.womanRank w m < p.womanRank w m')

/-- A partial matching is stable if its pairs are admissible and no admissible pair blocks it. -/
def IsPartialStable {n : ℕ} (p : Profile n) (A : Admissibility n)
    (M : PartialMatching n) : Prop :=
  (∀ e ∈ M.pairs, A e) ∧ ∀ m w, ¬ IsPartialBlockingPair p A M m w

private theorem isPartialBlockingPair_all_iff {n : ℕ} (p : Profile n)
    (μ : Matching n) (m w : Fin n) :
    IsPartialBlockingPair p (Admissibility.all n) μ.toPartialMatching m w ↔
      IsBlockingPair p μ m w := by
  simp only [IsPartialBlockingPair, Admissibility.all, true_and,
    mem_toPartialMatching_pairs, IsBlockingPair]
  constructor
  · rintro ⟨hm, hw⟩
    have h := hm (μ m) rfl
    refine ⟨?_, h, hw (μ.symm w) (μ.apply_symm_apply w)⟩
    rintro rfl
    exact (lt_irrefl _) h
  · rintro ⟨_, hm, hw⟩
    refine ⟨fun w' h ↦ h ▸ hm, ?_⟩
    intro m' h
    rw [μ.eq_symm_apply.mpr h]
    exact hw

/-- With every pair admissible, the two definitions of stability agree on complete matchings. -/
theorem isPartialStable_toPartialMatching_iff {n : ℕ} (p : Profile n) (μ : Matching n) :
    IsPartialStable p (Admissibility.all n) μ.toPartialMatching ↔ IsStable p μ := by
  simp only [IsPartialStable, IsStable, isPartialBlockingPair_all_iff]
  simp [Admissibility.all]

private theorem exists_matching_of_isPartialStable_all {n : ℕ} {p : Profile n}
    {M : PartialMatching n} (hStable : IsPartialStable p (Admissibility.all n) M) :
    ∃ μ : Matching n, μ.toPartialMatching = M := by
  classical
  have hmatch : ∀ m, ∃ w, (m, w) ∈ M.pairs := by
    intro m
    by_contra! hm
    have hw : ∀ w, ∃ m', (m', w) ∈ M.pairs := by
      intro w
      by_contra! h
      exact hStable.2 m w ⟨rfl, fun w' hw' ↦ (hm w' hw').elim, fun m' hm' ↦ (h m' hm').elim⟩
    choose husband hHusband using hw
    have hHusbandInj : Function.Injective husband := by
      intro w w' h
      exact congrArg Prod.snd (M.left_inj (hHusband w) (hHusband w') h)
    obtain ⟨w, rfl⟩ := Finite.surjective_of_injective hHusbandInj m
    exact hm w (hHusband w)
  choose wife hWife using hmatch
  have hWifeInj : Function.Injective wife := by
    intro m m' h
    exact congrArg Prod.fst (M.right_inj (hWife m) (hWife m') h)
  let μ := Equiv.ofBijective wife hWifeInj.bijective_of_finite
  refine ⟨μ, ?_⟩
  ext : 1
  ext ⟨m, w⟩
  simp only [mem_toPartialMatching_pairs, μ]
  constructor
  · rintro rfl
    exact hWife m
  · intro h
    exact congrArg Prod.snd (M.left_inj (hWife m) h rfl)

/-- With every pair admissible, stable partial matchings are exactly the pair sets of unique
stable complete matchings. -/
theorem isPartialStable_all_iff {n : ℕ} (p : Profile n) (M : PartialMatching n) :
    IsPartialStable p (Admissibility.all n) M ↔
      ∃! μ : Matching n, μ.toPartialMatching = M ∧ IsStable p μ := by
  constructor
  · intro h
    obtain ⟨μ, rfl⟩ := exists_matching_of_isPartialStable_all h
    refine ⟨μ, ⟨rfl, (isPartialStable_toPartialMatching_iff p μ).mp h⟩, ?_⟩
    intro ν hν
    apply Equiv.ext
    intro m
    apply (mem_toPartialMatching_pairs ν m (μ m)).mp
    rw [hν.1]
    simp
  · rintro ⟨μ, ⟨rfl, h⟩, _⟩
    exact (isPartialStable_toPartialMatching_iff p μ).mpr h

/-- One plus the number of admissible women whom `m` ranks ahead of `w`. -/
def wifeRank {n : ℕ} (p : Profile n) (A : Admissibility n) (m w : Fin n) : ℕ :=
  1 + (Finset.univ.filter fun v ↦ A (m, v) ∧ p.manRank m v < p.manRank m w).card

/-- One plus the number of admissible men whom `w` ranks ahead of `m`. -/
def husbandRank {n : ℕ} (p : Profile n) (A : Admissibility n) (m w : Fin n) : ℕ :=
  1 + (Finset.univ.filter fun u ↦ A (u, w) ∧ p.womanRank w u < p.womanRank w m).card

/-- The sum of the one-based ranks that matched men assign to their partners. -/
def totalWifeRank {n : ℕ} (p : Profile n) (A : Admissibility n) (M : PartialMatching n) : ℕ :=
  ∑ e ∈ M.pairs, wifeRank p A e.1 e.2

/-- The sum of the one-based ranks that matched women assign to their partners. -/
def totalHusbandRank {n : ℕ} (p : Profile n) (A : Admissibility n)
    (M : PartialMatching n) : ℕ :=
  ∑ e ∈ M.pairs, husbandRank p A e.1 e.2

private theorem card_filter_rank_lt {n : ℕ} (r : Equiv.Perm (Fin n)) (x : Fin n) :
    (Finset.univ.filter fun y ↦ r y < r x).card = (r x).val := by
  rw [← Finset.card_map r.toEmbedding, Finset.map_filter, Finset.map_univ_equiv]
  simp [Finset.filter_gt_eq_Iio]

/-- With every pair admissible, the total wife rank is the sum of the one-based preference ranks. -/
theorem totalWifeRank_toPartialMatching {n : ℕ} (p : Profile n) (μ : Matching n) :
    totalWifeRank p (Admissibility.all n) μ.toPartialMatching =
      ∑ m, (1 + (p.manRank m (μ m)).val) := by
  rw [totalWifeRank, Matching.toPartialMatching, Finset.sum_map]
  change (∑ m, wifeRank p (Admissibility.all n) m (μ m)) = _
  simp [wifeRank, Admissibility.all, card_filter_rank_lt]

/-- With every pair admissible, the total husband rank is the sum of the one-based preference
ranks. -/
theorem totalHusbandRank_toPartialMatching {n : ℕ} (p : Profile n) (μ : Matching n) :
    totalHusbandRank p (Admissibility.all n) μ.toPartialMatching =
      ∑ w, (1 + (p.womanRank w (μ.symm w)).val) := by
  rw [totalHusbandRank, Matching.toPartialMatching, Finset.sum_map]
  change (∑ m, husbandRank p (Admissibility.all n) m (μ m)) = _
  simpa [husbandRank, Admissibility.all, card_filter_rank_lt] using
    (Equiv.sum_comp μ fun w ↦ 1 + (p.womanRank w (μ.symm w)).val)

end StableMarriage
