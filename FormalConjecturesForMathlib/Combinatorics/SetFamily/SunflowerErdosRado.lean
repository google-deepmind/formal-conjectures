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

public import Mathlib.Tactic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Combinatorics.Pigeonhole
public import FormalConjecturesForMathlib.Combinatorics.SetFamily.Sunflower

@[expose] public section

/-!
# The Erdős–Rado sunflower bound

This file proves the Erdős–Rado factorial bound for sunflowers: every family $F$ of
$n$-uniform sets with at least $(k-1)^n \, n! + 1$ members contains a $k$-sunflower.
The reusable statement is `exists_sunflower_of_card_ge_erdosRadoBound`, proven by strong
induction on $n$ via a maximal pairwise-disjoint subfamily and a popular-point pigeonhole
argument on the link family.

*References:*
* [ErRa60] Erdős, Paul and Rado, Richard. Intersection theorems for systems of sets.
  J. London Math. Soc. 35 (1960), 85--90.
-/

open Set

/-- A pairwise-disjoint family is a sunflower (with empty kernel). -/
theorem isSunflower_of_pairwiseDisjoint {α : Type} (D : Set (Set α))
    (hD : D.PairwiseDisjoint id) : IsSunflower D := by
  refine ⟨∅, fun A hA B hB hAB => ?_⟩
  have := hD hA hB hAB
  simpa [Set.disjoint_iff_inter_eq_empty] using this

/-- From a pairwise-disjoint family of at least `k` sets, extract a `k`-sunflower. -/
theorem ksunflower_of_disjoint {α : Type} (D : Set (Set α)) (k : ℕ)
    (hDdisj : D.PairwiseDisjoint id) (hk : k ≤ D.ncard) :
    ∃ S ⊆ D, S.ncard = k ∧ IsSunflower S := by
  obtain ⟨S, hSsub, hScard⟩ := Set.exists_subset_card_eq hk
  exact ⟨S, hSsub, hScard, isSunflower_of_pairwiseDisjoint S (hDdisj.subset hSsub)⟩

/-- A family with at least `B ≥ 1` members (where `B ≤ F.ncard`) is finite. -/
theorem finite_of_bound_le_ncard {α : Type} (F : Set (Set α)) (B : ℕ) (hB : 1 ≤ B)
    (hle : B ≤ F.ncard) : F.Finite := by
  have hpos : 0 < F.ncard := lt_of_lt_of_le hB hle
  exact Set.finite_of_ncard_ne_zero (by omega)

/-- A finite family has a maximal pairwise-disjoint subfamily. -/
theorem exists_maximal_pairwiseDisjoint_subfamily {α : Type} (F : Set (Set α))
    (hFin : F.Finite) :
    ∃ D, Maximal (fun D' => D' ⊆ F ∧ D'.PairwiseDisjoint id) D := by
  set s : Set (Set (Set α)) := {D' | D' ⊆ F ∧ D'.PairwiseDisjoint id} with hs
  have hsFin : s.Finite := by
    apply Set.Finite.subset (hFin.finite_subsets)
    intro D' hD'
    exact hD'.1
  have hsNe : s.Nonempty := ⟨∅, by
    refine ⟨?_, ?_⟩
    · exact Set.empty_subset F
    · exact Set.pairwiseDisjoint_empty⟩
  obtain ⟨D, hD⟩ := hsFin.exists_maximal hsNe
  exact ⟨D, hD⟩

/-- For a maximal pairwise-disjoint subfamily `D` of an `n`-uniform family `F`, the union
`⋃₀ D` has cardinality `D.ncard * n` and meets every member of `F`. -/
theorem union_bound_and_covers {α : Type} (F : Set (Set α)) (n : ℕ) (hn : n > 0)
    (D : Set (Set α)) (hDsub : D ⊆ F) (hDdisj : D.PairwiseDisjoint id) (hDfin : D.Finite)
    (hunif : ∀ S ∈ F, S.ncard = n)
    (hmax : ∀ D', D' ⊆ F → D'.PairwiseDisjoint id → D ⊆ D' → D = D') :
    (⋃₀ D).ncard = D.ncard * n ∧ ∀ S ∈ F, (S ∩ ⋃₀ D).Nonempty := by
  refine ⟨?_, ?_⟩
  · have hfin_each : ∀ i ∈ D, (id i).Finite := by
      intro i hi
      simp only [id_eq]
      exact Set.finite_of_ncard_ne_zero (by rw [hunif i (hDsub hi)]; omega)
    have hset : ⋃₀ D = ⋃ i ∈ D, id i := by
      simp only [Set.sUnion_eq_biUnion, id_eq]
    rw [hset, Set.Finite.ncard_biUnion hDfin hfin_each hDdisj,
      finsum_mem_eq_finite_toFinset_sum (fun i => (id i).ncard) hDfin]
    have hval : ∀ i ∈ hDfin.toFinset, (id i).ncard = n := by
      intro i hi
      simp only [id_eq]
      exact hunif i (hDsub ((Set.Finite.mem_toFinset hDfin).mp hi))
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul]
    congr 1
    exact (Set.ncard_eq_toFinset_card D hDfin).symm
  · intro S hSF
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hSfin : S.Finite := Set.finite_of_ncard_ne_zero (by rw [hunif S hSF]; omega)
    have hSne : S.Nonempty := by
      rw [← Set.ncard_pos hSfin, hunif S hSF]; omega
    have hSnotD : S ∉ D := by
      intro hSD
      have hsub : S ⊆ ⋃₀ D := Set.subset_sUnion_of_mem hSD
      have hSI : S ∩ ⋃₀ D = S := Set.inter_eq_left.mpr hsub
      rw [hSI] at hempty
      exact hSne.ne_empty hempty
    have hdisj_new : (insert S D).PairwiseDisjoint id := by
      apply hDdisj.insert
      intro j hjD _hne
      simp only [id]
      rw [Set.disjoint_iff_inter_eq_empty]
      have hjsub : j ⊆ ⋃₀ D := Set.subset_sUnion_of_mem hjD
      have hsub2 : S ∩ j ⊆ S ∩ ⋃₀ D := Set.inter_subset_inter_right S hjsub
      rw [hempty] at hsub2
      exact Set.subset_eq_empty hsub2 rfl
    have hins_sub : insert S D ⊆ F := Set.insert_subset hSF hDsub
    have hDsubins : D ⊆ insert S D := Set.subset_insert S D
    have heq := hmax (insert S D) hins_sub hdisj_new hDsubins
    have hSmem : S ∈ D := heq ▸ Set.mem_insert S D
    exact hSnotD hSmem

/-- A popular-point pigeonhole: if `U.ncard * bound < F.ncard` and `U` meets every member of
`F`, some point `x ∈ U` lies in more than `bound` members of `F`. -/
theorem exists_popular_point {α : Type} (F : Set (Set α)) (U : Set α)
    (hFfin : F.Finite) (hUfin : U.Finite)
    (hcover : ∀ S ∈ F, (S ∩ U).Nonempty) (bound : ℕ)
    (hbig : U.ncard * bound < F.ncard) :
    ∃ x ∈ U, bound < {S ∈ F | x ∈ S}.ncard := by
  classical
  have hUne : U.Nonempty := by
    rcases U.eq_empty_or_nonempty with hU | hU
    · exfalso
      have hFpos : 0 < F.ncard := by
        have : U.ncard = 0 := by rw [hU]; simp
        rw [this] at hbig; simpa using hbig
      obtain ⟨S, hS⟩ := F.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨y, hy⟩ := hcover S hS
      rw [hU, Set.inter_empty] at hy
      exact absurd hy (Set.notMem_empty y)
    · exact hU
  obtain ⟨u₀, hu₀⟩ := hUne
  set g : Set α → α := fun S =>
    if h : (S ∩ U).Nonempty then h.choose else u₀ with hg_def
  have hgU : ∀ S ∈ F, g S ∈ U := by
    intro S hS
    have h := hcover S hS
    simp only [hg_def, dif_pos h]
    exact h.choose_spec.2
  have hgS : ∀ S ∈ F, g S ∈ S := by
    intro S hS
    have h := hcover S hS
    simp only [hg_def, dif_pos h]
    exact h.choose_spec.1
  have hmaps : ∀ S ∈ hFfin.toFinset, g S ∈ hUfin.toFinset := by
    intro S hS
    rw [Set.Finite.mem_toFinset] at hS ⊢
    exact hgU S hS
  have hcardF : F.ncard = hFfin.toFinset.card := Set.ncard_eq_toFinset_card F hFfin
  have hcardU : U.ncard = hUfin.toFinset.card := Set.ncard_eq_toFinset_card U hUfin
  have hbig' : hUfin.toFinset.card * bound < hFfin.toFinset.card := by
    rw [← hcardF, ← hcardU]; exact hbig
  obtain ⟨y, hyU, hy⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hbig'
  rw [Set.Finite.mem_toFinset] at hyU
  refine ⟨y, hyU, ?_⟩
  set fiber : Finset (Set α) := {S ∈ hFfin.toFinset | g S = y} with hfiber_def
  have hsub : (fiber : Set (Set α)) ⊆ {S ∈ F | y ∈ S} := by
    intro S hS
    simp only [hfiber_def, Finset.coe_filter, Set.mem_ofPred_eq,
      Set.Finite.mem_toFinset] at hS
    obtain ⟨hSF, hSy⟩ := hS
    refine ⟨hSF, ?_⟩
    rw [← hSy]
    exact hgS S hSF
  have hfin_target : {S ∈ F | y ∈ S}.Finite := hFfin.subset (fun S hS => hS.1)
  have hle : (fiber.card : ℕ) ≤ {S ∈ F | y ∈ S}.ncard := by
    rw [← Set.ncard_coe_finset fiber]
    exact Set.ncard_le_ncard hsub hfin_target
  calc bound < fiber.card := hy
    _ ≤ {S ∈ F | y ∈ S}.ncard := hle

/-- The link family `{S \ {x} | S ∈ Fx}` of an `(m+1)`-uniform family `Fx` all containing `x`:
it is `m`-uniform, equinumerous with `Fx`, and none of its members contain `x`. -/
theorem link_family {α : Type} (Fx : Set (Set α)) (x : α) (m : ℕ)
    (hmemx : ∀ S ∈ Fx, x ∈ S) (hunif : ∀ S ∈ Fx, S.ncard = m + 1) :
    (∀ T ∈ (fun S => S \ {x}) '' Fx, T.ncard = m) ∧
      ((fun S => S \ {x}) '' Fx).ncard = Fx.ncard ∧
      (∀ T ∈ (fun S => S \ {x}) '' Fx, x ∉ T) := by
  have hSfin : ∀ S ∈ Fx, S.Finite := by
    intro S hS
    exact Set.finite_of_ncard_ne_zero (by rw [hunif S hS]; omega)
  have hrecover : ∀ S ∈ Fx, insert x (S \ {x}) = S := by
    intro S hS
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem (hmemx S hS)]
  have hinj : Set.InjOn (fun S => S \ {x}) Fx := by
    intro A hA B hB hEq
    simp only at hEq
    have : insert x (A \ {x}) = insert x (B \ {x}) := by rw [hEq]
    rwa [hrecover A hA, hrecover B hB] at this
  refine ⟨?_, ?_, ?_⟩
  · rintro T ⟨S, hS, rfl⟩
    simp only
    have hxnot : x ∉ S \ {x} := fun h => h.2 rfl
    have hfin : (S \ {x}).Finite := (hSfin S hS).subset Set.sdiff_subset
    have hcard : (insert x (S \ {x})).ncard = (S \ {x}).ncard + 1 :=
      Set.ncard_insert_of_notMem hxnot hfin
    rw [hrecover S hS, hunif S hS] at hcard
    omega
  · exact hinj.ncard_image
  · rintro T ⟨S, hS, rfl⟩
    exact fun h => h.2 rfl

/-- Lift a `k`-sunflower in `G` (none of whose members contain `x`) to a `k`-sunflower in
`(insert x ·) '' G` by inserting `x` into every set. -/
theorem sunflower_insert_point {α : Type} (G : Set (Set α)) (x : α) (k : ℕ) (Tfam : Set (Set α))
    (hTsub : Tfam ⊆ G) (hTcard : Tfam.ncard = k) (hTsun : IsSunflower Tfam)
    (hxnotmem : ∀ T ∈ G, x ∉ T) :
    ∃ Sfam ⊆ (fun T => insert x T) '' G, Sfam.ncard = k ∧ IsSunflower Sfam := by
  classical
  have hxnotmemT : ∀ T ∈ Tfam, x ∉ T := fun T hT => hxnotmem T (hTsub hT)
  have hinj : Set.InjOn (fun T => insert x T) Tfam := by
    intro A hA B hB hEq
    have hxA : x ∉ A := hxnotmemT A hA
    have hxB : x ∉ B := hxnotmemT B hB
    simp only at hEq
    have hA' : (insert x A) \ {x} = A := by
      ext y
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hy1 | hy1, hy2⟩
        · exact absurd hy1 hy2
        · exact hy1
      · intro hy
        refine ⟨Or.inr hy, ?_⟩
        rintro rfl
        exact hxA hy
    have hB' : (insert x B) \ {x} = B := by
      ext y
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hy1 | hy1, hy2⟩
        · exact absurd hy1 hy2
        · exact hy1
      · intro hy
        refine ⟨Or.inr hy, ?_⟩
        rintro rfl
        exact hxB hy
    have : (insert x A) \ {x} = (insert x B) \ {x} := by rw [hEq]
    rwa [hA', hB'] at this
  refine ⟨(fun T => insert x T) '' Tfam, Set.image_mono hTsub, ?_, ?_⟩
  · rw [hinj.ncard_image, hTcard]
  · obtain ⟨S, hS⟩ := hTsun
    refine ⟨insert x S, ?_⟩
    unfold IsSunflowerWithKernel at hS ⊢
    rintro A' ⟨A, hA, rfl⟩ B' ⟨B, hB, rfl⟩ hne
    have hAB : A ≠ B := by
      rintro rfl
      exact hne rfl
    have hxA : x ∉ A := hxnotmemT A hA
    have hxB : x ∉ B := hxnotmemT B hB
    have hinter : A ∩ B = S := hS hA hB hAB
    have : insert x A ∩ insert x B = insert x (A ∩ B) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨hy1 | hy1, hy2 | hy2⟩
        · exact Or.inl hy1
        · exact Or.inl hy1
        · exact Or.inl hy2
        · exact Or.inr ⟨hy1, hy2⟩
      · rintro (rfl | ⟨hy1, hy2⟩)
        · exact ⟨Or.inl rfl, Or.inl rfl⟩
        · exact ⟨Or.inr hy1, Or.inr hy2⟩
    rw [this, hinter]

/-- The arithmetic identity `(k-1)(m+1) · (k-1)^m m! = (k-1)^{m+1} (m+1)!` powering the induction
step of the Erdős–Rado bound. -/
theorem arith_identity (k m : ℕ) :
    (k - 1) * (m + 1) * ((k - 1) ^ m * m.factorial) = (k - 1) ^ (m + 1) * (m + 1).factorial := by
  rw [Nat.factorial_succ, pow_succ]
  ring

/-- **The Erdős–Rado sunflower bound.** Proven by strong induction on `n`: every `n`-uniform
family `F` with at least `(k-1)^n n! + 1` members contains a `k`-sunflower. -/
theorem exists_sunflower_of_card_ge_erdosRadoBound :
    ∀ n, 0 < n → ∀ k, 2 ≤ k → ∀ {α : Type} (F : Set (Set α)),
      (∀ S ∈ F, S.ncard = n) → (k - 1) ^ n * n.factorial + 1 ≤ F.ncard →
      ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn k hk α F hunif hbig
    -- Bound B = (k-1)^n n! + 1 ≥ 1, so F is finite.
    have hB1 : 1 ≤ (k - 1) ^ n * n.factorial + 1 := by omega
    have hFfin : F.Finite := finite_of_bound_le_ncard F _ hB1 hbig
    -- Maximal pairwise-disjoint subfamily D.
    obtain ⟨D, hDmax⟩ := exists_maximal_pairwiseDisjoint_subfamily F hFfin
    obtain ⟨⟨hDsub, hDdisj⟩, hDmax2⟩ := hDmax
    have hDfin : D.Finite := hFfin.subset hDsub
    have hmax : ∀ D', D' ⊆ F → D'.PairwiseDisjoint id → D ⊆ D' → D = D' := by
      intro D' hD'sub hD'disj hDD'
      exact le_antisymm hDD' (hDmax2 ⟨hD'sub, hD'disj⟩ hDD')
    -- Case split on k ≤ D.ncard.
    by_cases hcase : k ≤ D.ncard
    · -- Pairwise-disjoint case applies directly.
      obtain ⟨S, hSsub, hScard, hSsun⟩ := ksunflower_of_disjoint D k hDdisj hcase
      exact ⟨S, hSsub.trans hDsub, hScard, hSsun⟩
    · -- D.ncard ≤ k - 1. Use the union bound + covering.
      push Not at hcase  -- D.ncard < k, i.e. D.ncard ≤ k - 1
      have hn_pos : 0 < n := (by omega : 0 < n)
      obtain ⟨hUcard, hcover⟩ :=
        union_bound_and_covers F n hn_pos D hDsub hDdisj hDfin hunif hmax
      set U := ⋃₀ D with hU_def
      -- U.ncard = D.ncard * n ≤ (k-1) * n
      have hUfin : U.Finite := by
        rw [hU_def]
        apply Set.Finite.sUnion hDfin
        intro S hS
        exact Set.finite_of_ncard_ne_zero (by rw [hunif S (hDsub hS)]; omega)
      have hUle : U.ncard ≤ (k - 1) * n := by
        rw [hUcard]
        have : D.ncard ≤ k - 1 := by omega
        exact Nat.mul_le_mul_right n this
      -- Now handle n via n = m + 1. Since n > 0.
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      -- Set the smaller bound b = (k-1)^m * m!.
      set b := (k - 1) ^ m * m.factorial with hb_def
      -- Pigeonhole precondition: U.ncard * b < F.ncard.
      have hkey : U.ncard * b < F.ncard := by
        have h1 : U.ncard * b ≤ (k - 1) * (m + 1) * b :=
          Nat.mul_le_mul_right b hUle
        have h2 : (k - 1) * (m + 1) * b = (k - 1) ^ (m + 1) * (m + 1).factorial := by
          rw [hb_def]; exact arith_identity k m
        have h3 : (k - 1) ^ (m + 1) * (m + 1).factorial < F.ncard := by omega
        calc U.ncard * b ≤ (k - 1) * (m + 1) * b := h1
          _ = (k - 1) ^ (m + 1) * (m + 1).factorial := h2
          _ < F.ncard := h3
      -- Popular point x.
      obtain ⟨x, hxU, hxpop⟩ := exists_popular_point F U hFfin hUfin hcover b hkey
      -- Fx = sets of F containing x.
      set Fx := {S ∈ F | x ∈ S} with hFx_def
      have hFxsub : Fx ⊆ F := fun S hS => hS.1
      have hFxfin : Fx.Finite := hFfin.subset hFxsub
      have hmemx : ∀ S ∈ Fx, x ∈ S := fun S hS => hS.2
      have hunifx : ∀ S ∈ Fx, S.ncard = m + 1 := fun S hS => hunif S (hFxsub hS)
      -- The link family G.
      obtain ⟨hGunif, hGcard, hGnox⟩ := link_family Fx x m hmemx hunifx
      set G := (fun S => S \ {x}) '' Fx with hG_def
      -- G.ncard = Fx.ncard > b, so bound (k-1)^m m! + 1 ≤ G.ncard.
      have hGbig : (k - 1) ^ m * m.factorial + 1 ≤ G.ncard := by
        rw [hGcard]
        omega
      -- Apply IH at m < m + 1 with same k.
      have hGfin : G.Finite := by
        rw [hG_def]; exact hFxfin.image _
      have hm_pos : 0 < m := by
        -- If m = 0, then G is 0-uniform, and (each member being finite) every member is ∅,
        -- so G ⊆ {∅} and G.ncard ≤ 1; but hGbig forces G.ncard ≥ 2. Contradiction.
        by_contra hm0
        push Not at hm0
        interval_cases m
        · have hGle1 : G.ncard ≤ 1 := by
            have hGsub : G ⊆ {∅} := by
              rintro T hT
              have hT0 : T.ncard = 0 := hGunif T hT
              -- T ∈ G means T = S \ {x} for S ∈ Fx, hence finite.
              obtain ⟨S, hS, rfl⟩ := hT
              have hSfin : S.Finite :=
                Set.finite_of_ncard_ne_zero (by rw [hunifx S hS]; omega)
              have hTfin : (S \ {x}).Finite := hSfin.subset Set.sdiff_subset
              have : (S \ {x}) = ∅ := (Set.ncard_eq_zero hTfin).mp hT0
              simp [this]
            calc G.ncard ≤ ({∅} : Set (Set α)).ncard :=
                  Set.ncard_le_ncard hGsub (Set.finite_singleton _)
              _ = 1 := Set.ncard_singleton _
          have hge : (k - 1) ^ 0 * (Nat.factorial 0) + 1 ≤ G.ncard := hGbig
          simp only [pow_zero, Nat.factorial_zero, one_mul] at hge
          omega
      obtain ⟨Tfam, hTsub, hTcard, hTsun⟩ :=
        IH m (by omega) hm_pos k hk G hGunif hGbig
      -- Lift sunflower in G back by inserting x.
      obtain ⟨Sfam, hSfamSub, hSfamCard, hSfamSun⟩ :=
        sunflower_insert_point G x k Tfam hTsub hTcard hTsun hGnox
      -- (fun T => insert x T) '' G ⊆ Fx ⊆ F: each insert x (S\{x}) = S ∈ Fx.
      have himg_sub : (fun T => insert x T) '' G ⊆ F := by
        rintro W ⟨T, hT, rfl⟩
        obtain ⟨S, hS, rfl⟩ := hT
        simp only
        rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem (hmemx S hS)]
        exact hFxsub hS
      exact ⟨Sfam, hSfamSub.trans himg_sub, hSfamCard, hSfamSun⟩
