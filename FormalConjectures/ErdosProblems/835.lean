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
open Finset

/-!
# Erdős Problem 835

*Reference:* [erdosproblems.com/835](https://www.erdosproblems.com/835)
-/
namespace Erdos835


/--
The property that for a given $k$, the $k$-subsets of a $2k$-set can be colored with $k+1$ colors
such that any $(k+1)$-subset contains all colors.
-/
def Property (k : ℕ) : Prop :=
  let K := {s : Finset (Fin (2 * k)) // s.card = k}
  ∃ c : K → Fin (k + 1),
    ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
      (image c {s : K | s.val ⊂ A}) = (univ : Finset (Fin (k+1)))

/--
Does there exist a $k>2$ such that the $k$-sized subsets of {1,...,2k} can be coloured with
$k+1$ colours such that for every $A\subset \{1,\ldots,2k\}$ with $\lvert A\rvert=k+1$ all $k+1$
colours appear among the $k$-sized subsets of $A$?
-/
@[category research open, AMS 5]
theorem erdos_835 : (∃ k > 2, Property k) ↔ answer(sorry) := by
  sorry

/--
The Johnson graph $J(n, k)$ has as vertices the $k$-subsets of an $n$-set.
Two vertices are adjacent if their intersection has size $k-1$.
Requires $k > 0$.
-/
def JohnsonGraph (n k : ℕ) (hk : 0 < k) : SimpleGraph {s : Finset (Fin n) // s.card = k} where
  Adj := λ S T => (S.val ∩ T.val).card = k - 1
  symm := by
    intro S T h
    rw [inter_comm]
    exact h
  loopless := by
    intro S h
    rw [inter_self] at h
    omega

@[category test, AMS 5]
theorem property_iff_chromaticNumber (k : ℕ) (hk : 0 < k) :
    ((JohnsonGraph (2 * k) k (Nat.zero_lt_of_lt hk)).chromaticNumber = k + 1) ↔
    Property k := by
  sorry

/--
Alternative statement of Erdős Problem 835 using the chromatic number of the Johnson graph.
This is equivalent to asking whether there exists $k > 2$ such that the chromatic number of the
Johnson graph $J(2k, k)$ is $k+1$.
-/
@[category research open, AMS 5]
theorem erdos_835.variant.johnson : (∃ l,
    -- making sure k > 2
    letI k := l + 3
    (JohnsonGraph (2 * k) k (by omega)).chromaticNumber = k + 1) ↔ answer(sorry) := by
  sorry

/--
It is known that for $3 \leq k \leq 8$, the chromatic number of $J(2k, k)$ is greater than $k+1$,
see [Johnson graphs](https://aeb.win.tue.nl/graphs/Johnson.html).
-/
@[category research solved, AMS 5]
theorem johnsonGraph_2k_k_chromaticNumber_known_cases (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) :
    (JohnsonGraph (2 * k) k (by omega)).chromaticNumber > k + 1 := by
  sorry

/--
The smallest open case is $k=9$. Is the chromatic number of $J(18, 9)$ equal to 10?

Answer: No!
-/
@[category research solved, AMS 5]
theorem johnsonGraph_18_9_chromaticNumber :
    ¬ (JohnsonGraph 18 9 (by omega)).chromaticNumber = 10 := by
  norm_num[JohnsonGraph,SimpleGraph.chromaticNumber]
  refine ne_of_gt<|lt_of_lt_of_le (show 10<11by decide) (le_iInf₂ fun and ⟨a, _⟩=>mod_cast Fintype.card_fin and▸? _)
  simp_all
  have:= Fintype.card_congr ((.sigmaFiberEquiv a))▸ Fintype.card_sigma.symm
  simp_all![Fintype.card_subtype]
  by_cases h : ∀y, Finset.biUnion {s | a s=y} (·.1.powersetCard 8) ⊆.powersetCard 8 .univ
  · replace h α :=((( Finset.card_biUnion) ?_).ge.trans ( Finset.card_mono (h α)) ).trans (by rw [ Finset.card_powersetCard _, Finset.card_fin])
    · simp_all![ Finset.sum_eq_card_nsmul]
      obtain ⟨@c⟩ :=eq_or_ne and 10
      · simp_all[ne_of_lt ∘(Finset.sum_le_sum fun and j=>(Nat.le_div_iff_mul_le _).2 (h _)).trans_lt]
        replace h y: Finset.card {s | a s=y}=43758/9:=le_antisymm ((Nat.le_div_iff_mul_le (by decide)).2 (h y)) (not_lt.1 fun and=>? _)
        · simp_all
          let α := Finset.univ.filter (a ·=0)
          have:α.biUnion (·.1.powersetCard 8) ⊆_:= Finset.biUnion_subset.2 fun and k=> Finset.powersetCard_mono and.1.subset_univ
          have:∑S ∈ α,∑T ∈.powersetCard 7 .univ,ite (T ⊆ S.val) (1) 0 = _:=α.sum_comm
          have : ∀ a ∈ Finset.univ.powersetCard 7,∑s ∈ α,ite (a ⊆ s.1) (1) 0≤5:=fun R M=> (α.card_filter _).ge.trans (not_lt.1 fun and=>? _)
          · use(( Finset.sum_le_sum this).trans_lt ?_).ne' (by valid)
            norm_num[ (by norm_num[ Finset.ext_iff,and_comm]:∀S: {x : Finset (Fin 18) //x.card=9},(Finset.univ.powersetCard 7).filter (. ⊆ S.val) = S.1.powersetCard 7), α,h]
            exact (α.sum_congr rfl fun and n=>by rw [and.2]).ge.trans_lt' (by norm_num[ α,Nat.choose_eq_factorial_div_factorial,h])
          replace: (α.filter (R ⊆·.1)).biUnion (·.1\R|>.powersetCard 1) ⊆(.univ\R).powersetCard (1):= fun and=>?_
          · apply(( Finset.card_mono this).trans_lt (by simp_all[←(2).div_lt_iff_lt_mul, Finset.sum_eq_card_nsmul, R.card_sdiff,Subtype.prop])).ne ∘ Finset.card_biUnion
            simp_rw [ α,Set.PairwiseDisjoint]at*
            simp_rw [Set.Pairwise,Finset.disjoint_left, Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_sdiff] at M⊢
            use fun and A B K V C _ _=>‹∀ (x _ _ _ _ _),_› and.1 (by use and.2) ( _) (by use B.prop) ?_<|by simp_all
            use le_antisymm (not_lt.1 fun and' =>V (and.eq (( Finset.eq_of_subset_of_card_le (by norm_num) (by valid)).symm.trans ( Finset.eq_of_subset_of_card_le and.1.inter_subset_right (by valid))))) (not_lt.1 fun and=>V ((Subtype.eq) ?_))
            cases(C∪R).card_mono (C.union_subset (by push_cast[*, C.subset_inter]:C ⊆Subtype.val (by gcongr) ∩B.val) ((by simp_all[ R.subset_inter]))) |>.not_lt (by simp_all[disjoint_comm])
          apply Finset.biUnion_subset.mpr @fun a s=> Finset.powersetCard_mono (a.val.sdiff_subset_sdiff a.val.subset_univ (by rw []))
        exact ( Finset.sum_lt_sum (fun R L=>(Nat.le_div_iff_mul_le (by decide)).2 (h R)) (by use y, Finset.mem_univ y)).ne this
      use (by valid ∘(Finset.sum_le_sum fun R L=>(Nat.le_div_iff_mul_le (by decide)).2 (h R)).trans_eq.comp ( Fin.sum_const _ _).trans) (mul_comm _ _)
    refine fun and R M A B=> Finset.disjoint_left.2 fun p K V=>‹∀ (x _ _ _ _ _),_› and.1 (by use and.2) M.1 (by use M.2) ?_<|by simp_all
    use le_antisymm (not_lt.1 fun and' =>B (and.eq (( Finset.eq_of_subset_of_card_le (by norm_num) (by valid)).symm.trans ( Finset.eq_of_subset_of_card_le and.1.inter_subset_right (by valid))))) (( Finset.mem_powersetCard.1 K).2▸? _)
    use p.card_mono (le_inf (Finset.mem_powersetCard.1 K).1 (Finset.mem_powersetCard.1 V).1)
  nlinarith [show 0 = 1 by aesop]



set_option maxHeartbeats 2000000 in
/--
Generalising to any odd k>9
-/
@[category research solved, AMS 5]
theorem johnsonGraph_chromaticNumber (l : ℕ) (hk : l > 6) (hl : Even l) :
    (JohnsonGraph (2*(l + 3)) (l + 3) (by omega)).chromaticNumber ≠  (l + 3) + 1 := by
  norm_num[JohnsonGraph,SimpleGraph.chromaticNumber]
  refine ne_of_gt<|lt_of_lt_of_le (show (l + 3 : ℕ∞) + 1< (l + 4) + 1 by norm_cast; norm_num) (le_iInf₂ fun and ⟨a, _⟩=>mod_cast Fintype.card_fin and▸? _)
  have:= Fintype.card_congr ((.sigmaFiberEquiv a))▸ Fintype.card_sigma.symm
  simp_all![Fintype.card_subtype]
  by_cases h : ∀y, Finset.biUnion {s | a s=y} (·.1.powersetCard (l+2)) ⊆.powersetCard (l + 2) .univ
  · replace h α :=((( Finset.card_biUnion) ?_).ge.trans ( Finset.card_mono (h α)) ).trans (by rw [ Finset.card_powersetCard _, Finset.card_fin])
    · simp_all![ Finset.sum_eq_card_nsmul]
      obtain ⟨@c⟩ :=eq_or_ne and (l + 4)
      · simp_all[ne_of_lt ∘(Finset.sum_le_sum fun and j=>(Nat.le_div_iff_mul_le _).2 (h _)).trans_lt]
        replace h y: Finset.card {s | a s=y}=((2*(l + 3)).choose (l + 2))/(l + 3):=le_antisymm ((Nat.le_div_iff_mul_le (by omega)).2 (show _ ≤  _ by refine le_of_le_of_eq (h y) ?_; rfl  )) (not_lt.1 fun and=>? _)
        · simp_all
          let α := Finset.univ.filter (a ·=0)
          have:α.biUnion (·.1.powersetCard (l + 2)) ⊆_:= Finset.biUnion_subset.2 fun and k=> Finset.powersetCard_mono and.1.subset_univ
          have:∑S ∈ α,∑T ∈.powersetCard (l + 1) .univ,ite (T ⊆ S.val) (1) 0 = _:=α.sum_comm
          --                                                                was  0≤5 -- what number to put here? perhaps (l + 5)/2 which is floor 5.5 = 5 for l = 6, k = 9
          have : ∀ a ∈ Finset.univ.powersetCard (l + 1),∑s ∈ α,ite (a ⊆ s.1) (1) 0≤(l + 5)/2:=fun R M=> (α.card_filter _).ge.trans (not_lt.1 fun and=>? _)
          · use(( Finset.sum_le_sum this).trans_lt ?_).ne' (by valid)
            norm_num[ (by norm_num[ Finset.ext_iff,and_comm]:∀S: {x : Finset (Fin (2 * (l + 3))) //x.card=(l + 3)},(Finset.univ.powersetCard (l + 1)).filter (. ⊆ S.val) = S.1.powersetCard (l + 1)), α,h]
            exact (α.sum_congr rfl fun and n=>by rw [and.2]).ge.trans_lt' (by norm_num[ α,Nat.choose_eq_factorial_div_factorial,h]; exact nat_choose_lemma1 l hk hl)
          replace: (α.filter (R ⊆·.1)).biUnion (·.1\R|>.powersetCard 1) ⊆(.univ\R).powersetCard (1):= fun and=>?_
          · apply(( Finset.card_mono this).trans_lt (by simp_all[←(2).div_lt_iff_lt_mul, Finset.sum_eq_card_nsmul, R.card_sdiff,Subtype.prop]; rw [show (2 * (l + 3) - (l + 1)) = l + 5 by omega];exact and)).ne ∘ Finset.card_biUnion
            simp_rw [ α,Set.PairwiseDisjoint]at*
            simp_rw [Set.Pairwise,Finset.disjoint_left, Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_sdiff] at M⊢
            use fun and A B K V C x_1 x_2=>‹∀ (x _ _ _ _ _),_› and.1 (by use and.2) ( _) (by use B.prop) ?_<|by simp_all
            norm_num at A K V
            apply Set.mem_setOf.2
            use le_antisymm (not_lt.1 fun and' =>V (and.eq (( Finset.eq_of_subset_of_card_le (R.union_subset A.2 x_1.1.1) ?_▸ Finset.eq_of_subset_of_card_le (R.union_subset K.2 x_2.1.1) ?_)))) ?_
            · norm_num[*, and.2,x_1.1.2.symm]
              cases V (and.eq (( Finset.eq_of_subset_of_card_le (by norm_num) (and.2.trans_le and')).symm.trans ( Finset.eq_of_subset_of_card_le (by norm_num) (B.2.trans_le and'))))
            · cases V (and.eq (( Finset.eq_of_subset_of_card_le (by norm_num) (and.2.trans_le and')).symm.trans ( Finset.eq_of_subset_of_card_le (by norm_num) (B.2.trans_le and'))))
            · apply M.2▸R.card_lt_card ⟨ R.subset_inter A.2 K.2,(C.card_pos).1 x_1.2.ge|>.elim fun and a s=> Finset.disjoint_left.1 x_1.1.2 a (s (by norm_num[x_1.1.1 _,x_2.1.1 _,a]))⟩
          apply Finset.biUnion_subset.mpr @fun a s=> Finset.powersetCard_mono (a.val.sdiff_subset_sdiff a.val.subset_univ (by rw []))
        have not_this :=  ( Finset.sum_lt_sum (fun R L=>(Nat.le_div_iff_mul_le (by omega)).2 (h R)) (by use y, Finset.mem_univ y;)).ne
        cases not_this.lt_or_lt
        · nlinarith[((2*(l+3)).choose (l+2)).mul_div_le (l+2+1), ( (2 *(l+3))).succ_mul_choose_eq (l+2), (2*(l+3)).choose_succ_succ (l+2), (by valid:).trans_eq (by rw [ Fin.sum_const,smul_eq_mul])]
        · use (by valid:).not_le (Finset.sum_le_sum fun R M=>(Nat.le_div_iff_mul_le (by valid)).2 (h R))
      rename_i h_1
      contrapose! this
      apply ne_of_lt.comp ( Finset.sum_le_card_nsmul _ _ _ fun and x =>(Nat.le_div_iff_mul_le (by valid)).2 (h _)).trans_lt
      norm_num[(mul_right_mono (and.le_of_lt_succ (h_1.lt_of_le (by valid)))).trans_lt.comp (Nat.mul_div_le _ _).trans_lt]
      exact (mul_right_mono (by valid:_≤l+3)).trans_lt ((Nat.mul_div_le _ _).trans_lt (by nlinarith[ (2 *(l+3)).succ_mul_choose_eq (l+2), (2*(l+3)).choose_pos (by valid:l+2≤ _), (2 *(l+3)).choose_succ_succ<|l+2]))
    refine fun and R M A B=> Finset.disjoint_left.2 fun p K V=>‹∀ (x _ _ _ _ _),_› and.1 (by use and.2) M.1 (by use M.2) ?_<|by simp_all
    apply Set.mem_setOf.2
    use(Finset.mem_powersetCard.1 K).elim fun a s=>le_antisymm (not_lt.1 (B ∘and.eq ∘?_)) (s.ge.trans (p.card_mono<|le_inf a (Finset.mem_powersetCard.1 V).1))
    exact ( Finset.eq_of_subset_of_card_le Finset.inter_subset_left |>.comp and.2.trans_le ·▸ Finset.eq_of_subset_of_card_le Finset.inter_subset_right (M.2.trans_le (by assumption)))
  nlinarith [show 0 = 1 by aesop]


end Erdos835
