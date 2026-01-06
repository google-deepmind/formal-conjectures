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
# Erdős Problem 477

*Reference:* [erdosproblems.com/477](https://www.erdosproblems.com/477)
-/

namespace Erdos477

open Polynomial Set

/--
Let $f = X ^ 2$ be a polynomial of degree at least $2$. Then there is not set
$A$ such that every $z\in \mathbb{Z}$ has exactly one representation as
$z=a+f(n)$ for some $a\in A$ and $n > 0$
-/
@[category research solved, AMS 12]
theorem erdos_477.variants.explicit_counterexample :
    letI f := X ^ 2
    ¬ ∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry


/--
Showing there are infinitely many exceptions of degree 2
-/
theorem erdos_477.variants.strong_negation_degree_two_dvd_condition_b_ne_zero
  (f : Polynomial ℤ) (hf₀ : 2 = f.degree)
  (hf_coeff : f.coeff 2 ∣ (f.coeff 1)) (hf_b : f.coeff 1 ≠ 0): ¬ ∃ (A : Set ℤ),
    ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  rintro ⟨A, hA⟩
  -- Step 1: A must be infinite
  have hA_inf : A.Infinite := by
    by_contra h_fin
    rw [Set.not_infinite] at h_fin
    -- A is finite, so A is bounded.
    have hA_bdd_below : BddBelow A := h_fin.bddBelow
    have hA_bdd_above : BddAbove A := h_fin.bddAbove

    let a := f.coeff 2
    let b := f.coeff 1
    let c := f.coeff 0

    have ha : a ≠ 0 := coeff_ne_zero_of_eq_degree hf₀.symm

    let S := f.eval '' {n | 0 < n}
    let sum_set := { x + y | (x ∈ A) (y ∈ S) }

    -- A covers Z implies sum_set = univ
    have h_univ : sum_set = univ := by
      ext z
      constructor
      · intro _; trivial
      · intro _
        obtain ⟨p, ⟨hp_mem, hp_eq⟩, _⟩ := hA z
        rw [mem_prod] at hp_mem
        simp only [sum_set, mem_setOf_eq]
        use p.1, hp_mem.1, p.2, hp_mem.2
        rw [hp_eq]

    cases lt_or_gt_of_ne ha with
    | inr ha_neg => -- a < 0
      have hS_bdd : BddAbove S := by
        norm_num[eval_eq_sum_range,natDegree_eq_of_degree_eq_some (hf₀.symm), Finset.sum_range_succ] at hA⊢
        cases l:lt_or_gt_of_ne (coeff_ne_zero_of_eq_degree (hf₀).symm)
        · use f.coeff 0+f.coeff (1)^2,Set.forall_mem_image.2 fun and i=>by nlinarith[pow_three (and-f.coeff (1))]
        obtain ⟨x,⟨⟨y,A, B, E⟩⟩,-⟩ :=hA (hA_bdd_below.some+f.coeff 0-f.coeff 1^2-1)
        nlinarith[sq (f.coeff (1)+A),hA_bdd_below.some_mem y]

      have h_bdd : BddAbove sum_set := by
        obtain ⟨bA, hbA⟩ := hA_bdd_above
        obtain ⟨bS, hbS⟩ := hS_bdd
        use bA + bS
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact add_le_add (hbA hx) (hbS hy)

      rw [h_univ] at h_bdd
      have : ¬ BddAbove (univ : Set ℤ) := not_bddAbove_univ
      exact this h_bdd

    | inl ha_pos => -- a > 0
      have hS_bdd : BddBelow S := by
         norm_num[eval_eq_sum_range,natDegree_eq_of_degree_eq_some (hf₀.symm), Finset.sum_range_succ] at hA ⊢
         cases l:lt_or_gt_of_ne ↑(coeff_ne_zero_of_eq_degree hf₀.symm)
         · obtain ⟨x,⟨⟨y,A, B, E⟩⟩,-⟩ :=hA (sSup A+(f.coeff 0+f.coeff (1)^2 + 1))
           nlinarith[pow_three (f.coeff (1)-A),le_csSup (by trivial) y]
         · use f.coeff 0-f.coeff 1^2,Set.forall_mem_image.2 fun a s=>by nlinarith[pow_three (f.coeff 1+2*f.coeff 2*a)]

      have h_bdd : BddBelow sum_set := by
        obtain ⟨bA, hbA⟩ := hA_bdd_below
        obtain ⟨bS, hbS⟩ := hS_bdd
        use bA + bS
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact add_le_add (hbA hx) (hbS hy)

      rw [h_univ] at h_bdd
      have : ¬ BddBelow (univ : Set ℤ) := not_bddBelow_univ
      exact this h_bdd

  -- Step 2: Difference set D
  let D := {d | ∃ n m : ℤ, 0 < n ∧ 0 < m ∧ f.eval n - f.eval m = d}

  -- Step 3: A - A intersects D \ {0}
  have h_collision : ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ a₂ ∧ a₁ - a₂ ∈ D := by
    let a := f.coeff 2
    let b := f.coeff 1
    have ha : a ≠ 0 := coeff_ne_zero_of_eq_degree hf₀.symm

    -- Step 3a: Prove D contains a homogeneous AP
    have h_D_hom : ∃ M > 0, ∃ C, ∀ k, M ∣ k → k > C → k ∈ D := by

      have h_identity : ∀ x y, f.eval x - f.eval y = (x - y) * (a * (x + y) + b) := by
        intro x y
        exact (.trans (by rw [eval_eq_sum_range,eval_eq_sum_range,natDegree_eq_of_degree_eq_some (hf₀.symm), Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]) (by ring))

      have h_identity' : ∀ x y, f.eval x - f.eval y = (x - y) * a * (x + y) + (x - y)*b := by
        intro x y
        have := h_identity x y
        rw [this]
        ring

      have : ∀ x d, f.eval (x + d) - f.eval x  =  2 *a* d* x + (b *d + a * d ^2) := by
        intro x d
        have :=  h_identity (x + d) x
        rw [this]
        ring

      have : ∀ x, f.eval (x + (-(b / a))) - f.eval x = 2 *a* (-b / a)* x := by
        intro x
        have := this x (-(b / a))
        simp  [mul_neg, neg_mul] at this
        rw [this]
        exact Int.neg_ediv_of_dvd hf_coeff▸by linear_combination .ediv_mul_cancel (hf_coeff) * (_/ _)

      let d := -(b / a)

      use |2 * b|
      -- We define a safe constant C to ensures inputs are positive.
      -- We need x > 0 and x + d > 0.
      -- x will be approx k / |2b|. So we need k > |2bd|.
      constructor
      · aesop
      use |d * 2 * b|

      intro k hk_div hk_C
      have hb : b ≠ 0 := by simp [b, hf_b]
      have h_M_pos : |2 * b| > 0 := abs_pos.mpr (by simp [hb])
      rcases lt_or_gt_of_ne hb with hb_neg | hb_pos
      · let x := k / (-2 * b)
        have hx_div : (-2 * b) ∣ k := by
          apply Dvd.dvd.trans ?_ hk_div
          norm_num

        constructor
        swap
        · use x + d
        · use x
          revert hx_div x hb_neg h_M_pos hk_C hk_div k d hb
          revert this
          revert this h_identity h_identity' ha b a D
          refine fun and A B a s R M N _ _ K V=>⟨by nlinarith only[ K,max_lt_iff.1 N,Int.ediv_mul_cancel V],by nlinarith only[ K,max_lt_iff.1 N,Int.ediv_mul_cancel V],s ( _)▸symm ?_⟩
          linear_combination-R.ediv_mul_cancel V-2*.ediv_mul_cancel (hf_coeff).neg_right*(R/ _)


      · let x := k / (2 * b)
        have hx_div : (2 * b) ∣ k := by
            rw [abs_of_pos (mul_pos two_pos hb_pos)] at hk_div
            exact hk_div

        use x, x + d
        revert hx_div x hb_pos h_M_pos hk_C hk_div k d hb
        revert this
        revert this h_identity h_identity' ha b a D
        use fun and _ _ _ a s R M _ _ _ α=>(max_lt_iff.1 M).elim fun A B=>⟨by nlinarith[s.ediv_mul_cancel α], ⟨by nlinarith[s.ediv_mul_cancel α] ,?_⟩⟩
        linear_combination s.ediv_mul_cancel α-a _-2*.ediv_mul_cancel (hf_coeff).neg_right*(s/ _)

    -- Step 3b: Use PHP to find collision
    have h_collision : ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ a₂ ∧ a₁ - a₂ ∈ D := by
      obtain ⟨M, hM_pos, C, hD_subset⟩ := h_D_hom
      revert hD_subset C hM_pos M
      use (hf_coeff.elim fun K V R M a s=>(exists_nat_gt (a-R)).elim fun and x =>by_contra fun and' =>(hA_inf) ? _)
      by_cases h:A.Finite
      · match R with | 1 => congr | 2 => congr | Nat.cast R + 3 => congr
      let α :=Set.Infinite.natEmbedding A h
      apply((Set.finite_Ico _ _).isCompact.isSeqCompact fun and' =>⟨ (α and').1.emod_nonneg M.ne', (α _).1.emod_lt_of_pos M⟩).elim
      norm_num(config := {singlePass:=1})at s and'⊢
      use fun _ _⟨A, B, S⟩=> S.exists_forall_of_atTop.elim fun K V=>?_
      by_cases h: BddAbove (( fun and=>abs ((α (A and)).1-α (A K))) ''.Ici K)
      · cases(Set.Ici_infinite _).mono (abs_le.1<|le_csSup h ⟨.,., rfl⟩) ((Set.finite_Icc _ _).preimage fun and _ _ _=>(B.injective<|α.2<|Subtype.eq<|sub_left_injective ·))
      convert h.elim ⟨R+and,Set.forall_mem_image.2 fun and (H) =>abs_le.2 ⟨not_lt.1 fun and => _,not_lt.1 fun and =>_⟩⟩
      · refine (and' _) ⟨ (α _).2, _, (α _).2,by omega,s ( _) ↑(Int.ModEq.symm (V K le_rfl▸ (V _) H).symm).dvd (by omega)⟩
      · use (and' _) ⟨ (α _).2, _, (α _).2,by omega,s ( _) ((Int.ModEq.symm (( (V _) H).trans (V K le_rfl).symm)).dvd) (by omega)⟩


    -- Identity: f(x) - f(y) = (x-y)(a(x+y)+b)
    have h_identity : ∀ x y, f.eval x - f.eval y = (x - y) * (a * (x + y) + b) := by
      intro x y
      exact (.trans (by rw [eval_eq_sum_range,eval_eq_sum_range,natDegree_eq_of_degree_eq_some (hf₀.symm), Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]) (by ring))

    have h_identity' : ∀ x y, f.eval x - f.eval y = (x - y) * a * (x + y) + (x - y)*b := by
      intro x y
      have := h_identity x y
      rw [this]
      ring

    have : ∀ x d, f.eval (x + d) - f.eval x  =  2 *a* d* x + (b *d + a * d ^2) := by
      intro x d
      have :=  h_identity (x + d) x
      rw [this]
      ring
    have : ∀ x, f.eval (x + (-(b / a))) - f.eval x = 2 *a* (-b / a)* x := by
      intro x
      have := this x (-(b / a))
      simp  [mul_neg, neg_mul] at this
      rw [this]
      exact Int.neg_ediv_of_dvd hf_coeff▸by linear_combination .ediv_mul_cancel (hf_coeff) * (_/ _)


    exact h_collision


  -- Step 4: Derive contradiction
  rcases h_collision with ⟨a₁, ha₁, a₂, ha₂, h_neq, h_diff⟩
  rcases h_diff with ⟨n, m, hn, hm, h_eq⟩
  -- a₁ - a₂ = f(n) - f(m) => a₁ + f(m) = a₂ + f(n)
  let z := a₁ + f.eval m
  have z_eq : z = a₂ + f.eval n := by
    rw [sub_eq_iff_eq_add] at h_eq
    rw [h_eq]
    ring

  -- Construct two distinct pairs
  let p1 : ℤ × ℤ := (a₁, f.eval m)
  let p2 : ℤ × ℤ := (a₂, f.eval n)

  have hp1 : p1 ∈ A ×ˢ (f.eval '' {k | 0 < k}) := by
    apply mk_mem_prod
    exact ha₁
    use m
    simp [hm]

  have hp2 : p2 ∈ A ×ˢ (f.eval '' {k | 0 < k}) := by
    apply mk_mem_prod
    exact ha₂
    use n
    simp [hn]

  have p1_sum : z = p1.1 + p1.2 := rfl
  have p2_sum : z = p2.1 + p2.2 := by dsimp; rw [z_eq]

  have p1_neq_p2 : p1 ≠ p2 := by
    intro h
    injection h with h_a h_f
    exact h_neq h_a

  -- Use uniqueness to show contradiction
  obtain ⟨p, _, h_unique⟩ := hA z
  have h1 := h_unique p1 ⟨hp1, p1_sum⟩
  have h2 := h_unique p2 ⟨hp2, p2_sum⟩
  rw [← h2] at h1
  exact p1_neq_p2 h1


/--
Probably there is no such $A$ for any polynomial $f$ of degree $2$.
-/
@[category research open, AMS 12]
theorem erdos_477.variants.strong_negation_degree_eq_two (f : Polynomial ℤ) (hf₀ : 2 = f.degree) :
    ¬ ∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry


/--
Probably there is no such $A$ for the polynomial $X^3$.
-/
@[category research open, AMS 12]
theorem erdos_477.variants.strong_negation_pow_three :
    letI f := X ^ 3
    ¬ ∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry

/--
Probably there is no such $A$ for the polynomial $X^k$ for any $k \ge 0$.
-/
@[category research open, AMS 12]
theorem erdos_477.variants.strong_negation_monomial (k : ℕ) (hk : 2 ≤ k):
    letI f := X ^ k
    ¬ ∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry

/--
Let $f:\mathbb{Z}\to \mathbb{Z}$ be a polynomial of degree at least $2$. Is there a set $A$ such
that every $z\in \mathbb{Z}$ has exactly one representation as $z=a+f(n)$ for some $a\in A$ and
$n > 0$?
-/
@[category research solved, AMS 12]
theorem erdos_477 : answer(False) ↔ ∀ (f : Polynomial ℤ), 2 ≤ f.degree →
    (∃ (A : Set ℤ), ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2) := by
  simp only [false_iff, not_forall]
  exact ⟨.X ^ 2, by simp, erdos_477.variants.explicit_counterexample⟩

/--
Probably there is no such $A$ for any polynomial $f$.
-/
@[category research open, AMS 12]
theorem erdos_477.variants.strong_negation (f : Polynomial ℤ) (hf₀ : 2 ≤ f.degree) :
    ¬ ∃ A : Set ℤ, ∀ z, ∃! a ∈ A ×ˢ (f.eval '' {n | 0 < n}), z = a.1 + a.2 := by
  sorry

end Erdos477
